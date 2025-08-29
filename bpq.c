// bpqchat.c — Client BPQ stile chat con ncurses (wide/UTF-8 safe) + local echo + RX line accumulator + Ctrl-Z
//
//  • Output verde in alto (soft-wrap wide-safe, scroll PgUp/PgDn/↑/↓/Home/End)
//  • Barra comandi bianca fissa in basso; cursore sempre lì (wide)
//  • Reflow al resize (wrap coerente con cols-1)
//  • Telnet minimal (IAC/DO/DONT/WILL/WONT/SB/SE), cap-safe + TX IAC escaping
//  • RX: normalizza CR/LF; TX: CRLF (o solo CR con --cr-only)
//  • Autologin (prompt + cieco); invio automatico “?” dopo sblocco (se abilitato)
//  • TAB espansi a spazi (tabstop 8) per wrapping corretto
//  • SIGPIPE ignorato, write() robusto
//  • Local echo: comandi inviati appaiono anche nell’output (disattivabile con --no-local-echo)
//  • RX accumulator: nessuna riga viene spezzata su confini di pacchetto (righe solo su '\n')
//  • Ctrl-Z: inviato al nodo come 0x1A (SUB); opzionale sospensione UNIX con --no-pass-ctrl-z
//
// Build: gcc -O2 -Wall -o bpqchat bpqchat.c -lncursesw
// Uso  : ./bpqchat <host> <port>
//        [-u USER -p PASS] [--blind-auto] [--cr-only] [--upper] [--no-auto-help] [--no-local-echo]
//        [--no-pass-ctrl-z] [--ctrl-z-cr]
// Opz. : --unlock-delay MS (default 1200), --unlock-quiet MS (default 300)

#define _POSIX_C_SOURCE 200809L
#include <ncurses.h>
#include <locale.h>
#include <errno.h>
#include <ctype.h>
#include <netdb.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>
#include <wchar.h>
#include <wctype.h>

/* Telnet */
enum { IAC=255, DONT=254, DO_=253, WONT=252, WILL=251, SB=250, SE=240 };

/* UI */
static int sockfd=-1;
static WINDOW *win_out=NULL, *win_status=NULL, *win_in=NULL;
static int rows=0, cols=0;
static const char *PROMPT="> ";

/* Opzioni */
static int opt_cr_only=0, opt_upper=0, opt_auto_help=1;
static int opt_local_echo=1;            /* echo locale attivo di default */
static int opt_pass_ctrl_z=1;           /* default: passa ^Z (0x1A) al nodo */
static int opt_ctrlz_append_cr=0;       /* dopo ^Z, invia anche EOL se settato */
static long unlock_delay_ms=1200, unlock_quiet_ms=300;

/* Colori */
#define CP_OUT 1  /* verde */
#define CP_IN  2  /* bianco */
#define CP_ST  3  /* ciano */

/* Stato output: archivio righe logiche wide + righe visuali wide wrappate */
#define STORE_MAX 20000
#define VIS_MAX   200000
static wchar_t *store[STORE_MAX];  static int store_count=0;
static wchar_t *visual[VIS_MAX];   static int vis_count=0;
static int view_top=0; /* indice prima riga visuale mostrata */

/* Varie */
static volatile sig_atomic_t need_resize=0;
static const int TABSTOP=8;

/* Accumulatore RX (UTF-8) per evitare spezzature di riga tra chunk */
static char  *rx_acc = NULL;
static size_t rx_len = 0, rx_cap = 0;

/* Utils di tempo */
static long since_ms(struct timespec a, struct timespec b){
    return (b.tv_sec-a.tv_sec)*1000 + (b.tv_nsec-a.tv_nsec)/1000000;
}

/* ---- Low-level I/O ---- */
static ssize_t write_all(int fd, const void *buf, size_t len){
    const unsigned char *p = (const unsigned char*)buf;
    size_t left = len;
    while (left>0){
        ssize_t w = write(fd, p, left);
        if (w<0){
            if (errno==EINTR) continue;
            return -1;
        }
        p+=w; left-=w;
    }
    return (ssize_t)len;
}
static void die_cleanup(const char*fmt, ...) {
    if (sockfd>=0) close(sockfd);
    if (win_out || win_status || win_in) endwin();
    for (int i=0;i<store_count;i++) free(store[i]);
    for (int i=0;i<vis_count;i++) free(visual[i]);
    free(rx_acc);
    if (fmt) {
        va_list ap; va_start(ap, fmt); vfprintf(stderr, fmt, ap); va_end(ap);
        fputc('\n', stderr);
        exit(EXIT_FAILURE);
    }
    exit(EXIT_SUCCESS);
}
static void on_winch(int sig){ (void)sig; need_resize=1; }

/* ---------- Telnet minimal cap-safe ---------- */
typedef struct { int state; unsigned char cmd; } telnet_parser_t;
static void telnet_send3(unsigned char a,unsigned char b,unsigned char c){
    unsigned char t[3]={a,b,c}; if (write_all(sockfd,t,3)<0) die_cleanup("write telnet: %s", strerror(errno));
}
static size_t telnet_filter_and_reply(telnet_parser_t *tp,
                                      const unsigned char *in, size_t len,
                                      unsigned char *out, size_t outcap)
{
    size_t o=0;
    for (size_t i=0;i<len;i++){
        unsigned char ch=in[i];
        switch (tp->state){
            case 0:
                if (ch==IAC) tp->state=1;
                else if (o<outcap) out[o++]=ch;
                break;
            case 1:
                tp->cmd=ch;
                if (ch==IAC){ if (o<outcap) out[o++]=IAC; tp->state=0; }
                else if (ch==DO_||ch==DONT||ch==WILL||ch==WONT) tp->state=2;
                else if (ch==SB) tp->state=3;
                else if (ch==SE) tp->state=0;
                else tp->state=0;
                break;
            case 2:{
                unsigned char opt=ch;
                if (tp->cmd==DO_) telnet_send3(IAC,WONT,opt);
                else if (tp->cmd==WILL) telnet_send3(IAC,DONT,opt);
                tp->state=0; break;
            }
            case 3: if (ch==IAC) tp->state=4; break;
            case 4: if (ch==SE) tp->state=0; else tp->state=3; break;
        }
    }
    return o;
}

/* ---------- RX newline normalize ---------- */
static size_t normalize_incoming(const unsigned char *in,size_t len,unsigned char *out,size_t outcap){
    size_t o=0;
    for (size_t i=0;i<len;i++){
        unsigned char ch=in[i];
        if (ch=='\r'){
            if (i+1<len && in[i+1]=='\n'){ if (o<outcap) out[o++]='\n'; i++; }
            else { if (o<outcap) out[o++]='\n'; }
        } else if (ch=='\n'){
            if (o<outcap) out[o++]='\n';
        } else {
            if (o<outcap) out[o++]=ch;
        }
    }
    return o;
}

/* ---------- TCP ---------- */
static int connect_tcp(const char*host,const char*port){
    struct addrinfo hints,*res,*rp; int fd=-1;
    memset(&hints,0,sizeof hints); hints.ai_family=AF_UNSPEC; hints.ai_socktype=SOCK_STREAM;
    int err=getaddrinfo(host,port,&hints,&res);
    if (err) die_cleanup("getaddrinfo: %s", gai_strerror(err));
    for (rp=res; rp; rp=rp->ai_next){
        fd=socket(rp->ai_family,rp->ai_socktype,rp->ai_protocol);
        if (fd==-1) continue;
        if (connect(fd,rp->ai_addr,rp->ai_addrlen)==0) break;
        close(fd); fd=-1;
    }
    freeaddrinfo(res);
    if (fd<0) die_cleanup("connect fallita");
    return fd;
}

/* ---------- UI ---------- */
static void ui_make_windows(void){
    if (win_out) { delwin(win_out); win_out=NULL; }
    if (win_status) { delwin(win_status); win_status=NULL; }
    if (win_in) { delwin(win_in); win_in=NULL; }

    int out_h = rows - 2; if (out_h < 1) out_h = 1;
    win_out    = newwin(out_h, cols, 0, 0);
    win_status = newwin(1, cols, out_h, 0);
    win_in     = newwin(1, cols, out_h+1, 0);

    wbkgd(win_out,    COLOR_PAIR(CP_OUT));
    wbkgd(win_status, COLOR_PAIR(CP_ST));
    wbkgd(win_in,     COLOR_PAIR(CP_IN));

    scrollok(win_out, FALSE);
    keypad(stdscr, TRUE);
    keypad(win_in, TRUE);
    curs_set(1);

    werase(win_status);
    mvwprintw(win_status, 0, 0, "Output SOPRA (verde) — Comandi QUI (bianco). PgUp/PgDn/↑/↓/Home/End. F10 o Ctrl-C: esci. Ctrl-Z: SUB");
    wrefresh(win_status);
}
static void ui_init(void){
    setlocale(LC_ALL, "");
    initscr(); cbreak(); noecho(); timeout(50);
    start_color(); use_default_colors();
    init_pair(CP_OUT, COLOR_GREEN, -1);
    init_pair(CP_IN,  COLOR_WHITE, -1);
    init_pair(CP_ST,  COLOR_CYAN,  -1);
    getmaxyx(stdscr, rows, cols);
    ui_make_windows();
}

/* ---------- Wide helpers (UTF-8 <-> wide) ---------- */
static wchar_t *utf8_to_wcs_lossy(const char *s){
    if (!s) return wcsdup(L"");
    size_t n = strlen(s);
    mbstate_t st; memset(&st,0,sizeof st);
    const char *p = s;
    size_t cap = n+1;
    wchar_t *out = (wchar_t*)malloc(sizeof(wchar_t)*cap);
    if (!out) return NULL;
    size_t o=0;
    while (*p){
        wchar_t wc=0;
        size_t r = mbrtowc(&wc, p, MB_CUR_MAX, &st);
        if (r==(size_t)-2){ wc=L'?'; r=1; memset(&st,0,sizeof st); }
        else if (r==(size_t)-1){ wc=L'?'; r=1; memset(&st,0,sizeof st); }
        else if (r==0){ wc=L'\0'; p++; }
        if (o+1>=cap){ cap = cap*2 + 8; wchar_t *tmp=realloc(out,sizeof(wchar_t)*cap); if(!tmp){ free(out); return NULL; } out=tmp; }
        out[o++]=wc;
        p += (r==0?1:r);
    }
    out[o]=L'\0';
    return out;
}

/* Espansione TAB -> spazi, tabstop in colonne visuali */
static wchar_t *expand_tabs_wcs(const wchar_t *in, int tabstop){
    if (!in) return wcsdup(L"");
    size_t cap = wcslen(in) + 1;
    wchar_t *out = (wchar_t*)malloc(sizeof(wchar_t)*cap);
    if (!out) return NULL;
    size_t o=0;
    int col=0;
    for (size_t i=0; in[i]; ++i){
        wchar_t ch = in[i];
        int w = wcwidth(ch);
        if (ch==L'\t'){
            int next = tabstop>0 ? ((col/tabstop)+1)*tabstop : col+1;
            int spaces = next - col;
            if (spaces<1) spaces=1;
            if (o+spaces+1>=cap){ cap = cap + spaces + 64; wchar_t *tmp=realloc(out,sizeof(wchar_t)*cap); if(!tmp){ free(out); return NULL; } out=tmp; }
            for (int k=0;k<spaces;k++){ out[o++]=L' '; }
            col = next;
            continue;
        }
        if (w<0) w=1; /* non stampabili: considerali 1 */
        if (o+1>=cap){ cap = cap*2 + 8; wchar_t *tmp=realloc(out,sizeof(wchar_t)*cap); if(!tmp){ free(out); return NULL; } out=tmp; }
        out[o++]=ch;
        col += w;
    }
    out[o]=L'\0';
    return out;
}

/* ---------- Store & wrap visual (wide) ---------- */
static void free_visual(void){ for (int i=0;i<vis_count;i++) free(visual[i]); vis_count=0; }
static void push_visual_w(const wchar_t *s){
    if (!s) s=L"";
    wchar_t *copy = wcsdup(s); if (!copy) return;
    if (vis_count < VIS_MAX) visual[vis_count++] = copy;
    else {
        free(visual[0]);
        memmove(visual, visual+1, sizeof(visual[0])*(VIS_MAX-1));
        visual[VIS_MAX-1] = copy;
        if (view_top>0) view_top--;
    }
}

/* wrap su colonne visuali, evitando split di codepoint; preferisci taglio a spazi/punteggiatura */
static void wrap_and_push_wide(const wchar_t *line, int width){
    if (width < 1) width = 1;
    size_t len = wcslen(line);
    size_t i = 0;
    while (i < len){
        size_t start = i;
        int col=0, overflow=0;
        ssize_t last_break = -1;
        int col_at_last_break = 0;

        while (i < len){
            wchar_t ch = line[i];
            int w = wcwidth(ch);
            if (w < 0) w = 1; /* fallback */
            /* opportunità di taglio */
            if (ch==L' ' || iswpunct(ch)) { last_break = (ssize_t)i; col_at_last_break = col + w; }

            if (col + w > width){ overflow=1; break; }

            col += w; i++;
            if (col==width) { break; }
        }

        size_t end = i;
        if (overflow){
            if (last_break >= (ssize_t)start && col_at_last_break>0){
                end = (size_t)last_break + 1;
            } else if (end==start){
                /* char più largo del width: forza presa di almeno un char */
                end = start + 1;
            }
        }

        /* copia segmento [start,end) */
        size_t seglen = end - start;
        wchar_t *seg = (wchar_t*)malloc(sizeof(wchar_t)*(seglen+1));
        if (!seg) return;
        wmemcpy(seg, line+start, seglen); seg[seglen]=L'\0';
        push_visual_w(seg);
        free(seg);

        /* salta spazi successivi all'interruzione per non iniziare la nuova riga con spazio */
        while (end < len && line[end]==L' ') end++;
        i = end;
    }
}

static void add_logical_line_w(const wchar_t *line, int follow){
    wchar_t *copy = wcsdup(line?line:L""); if (!copy) return;
    if (store_count < STORE_MAX) store[store_count++]=copy;
    else { free(store[0]); memmove(store, store+1, sizeof(store[0])*(STORE_MAX-1)); store[STORE_MAX-1]=copy; }

    int width = cols - 1; if (width<1) width=1;
    wrap_and_push_wide(line, width);
    if (follow) {
        int visible = rows-2; if (visible<1) visible=1;
        view_top = vis_count - visible; if (view_top<0) view_top=0;
    }
}
static void reflow(int keep_bottom){
    free_visual();
    int width = cols - 1; if (width<1) width=1;
    for (int i=0;i<store_count;i++) wrap_and_push_wide(store[i], width);
    int visible = rows-2; if (visible<1) visible=1;
    if (keep_bottom) {
        view_top = vis_count - visible; if (view_top<0) view_top=0;
    } else {
        int max_top = vis_count - visible; if (max_top<0) max_top=0;
        if (view_top>max_top) view_top=max_top;
        if (view_top<0) view_top=0;
    }
}

/* ---------- Render ---------- */
static void render_out(void){
    werase(win_out);
    int visible = rows - 2; if (visible<1) visible=1;
    int max_top = vis_count - visible; if (max_top<0) max_top=0;
    if (view_top>max_top) view_top=max_top;
    int y=0;
    for (int i=view_top; i<vis_count && y<visible; ++i,++y) {
        if (cols>0) mvwaddnwstr(win_out, y, 0, visual[i], wcslen(visual[i]));
    }
    wrefresh(win_out);
}
static size_t tail_offset_fit(const wchar_t *buf, int maxcols){
    if (maxcols <= 0) return wcslen(buf);
    size_t len = wcslen(buf);
    int col=0;
    ssize_t start = (ssize_t)len;
    for (ssize_t i=(ssize_t)len-1; i>=0; --i){
        int w = wcwidth(buf[i]); if (w<0) w=1;
        if (col + w > maxcols) break;
        col += w; start = i;
    }
    return (size_t)start;
}

static void render_input(const wchar_t *buf){
    werase(win_in);
    int room = cols - (int)strlen(PROMPT) - 1; if (room < 0) room = 0;
    size_t start = tail_offset_fit(buf, room);
    mvwprintw(win_in, 0, 0, "%s", PROMPT);
    waddnwstr(win_in, buf + start, wcslen(buf + start));
    wmove(win_in, 0, (int)strlen(PROMPT) + (int)wcswidth(buf + start, wcslen(buf + start)));
    wrefresh(win_in);
}

/* ---------- Helpers TX ---------- */
static void send_eol(void){
    if (opt_cr_only){ char cr='\r'; if (write_all(sockfd,&cr,1)<0) die_cleanup("write: %s", strerror(errno)); }
    else { char crlf[2]={'\r','\n'}; if (write_all(sockfd,crlf,2)<0) die_cleanup("write: %s", strerror(errno)); }
}

/* Duplica ogni IAC (0xFF) in TX, con write_all */
static void write_telnet_safe(const unsigned char *s, size_t n){
    for (size_t i=0;i<n;i++){
        unsigned char c = s[i];
        if (write_all(sockfd, &c, 1)<0) die_cleanup("write: %s", strerror(errno));
        if (c == IAC){
            if (write_all(sockfd, &c, 1)<0) die_cleanup("write: %s", strerror(errno));
        }
    }
}

static void send_line_utf8_telnet_safe(const char*s){ write_telnet_safe((const unsigned char*)s, strlen(s)); send_eol(); }

/* Case-insensitive strstr */
static const char* istrstr(const char*hay,const char*needle){
    if(!*needle) return hay; size_t nlen=strlen(needle);
    for(const char*p=hay; *p; ++p){
        if (tolower((unsigned char)*p)==tolower((unsigned char)*needle))
            if (strncasecmp(p,needle,nlen)==0) return p;
    }
    return NULL;
}

/* ---------- Autologin ---------- */
typedef struct { int enabled; int state; char user[128]; char pass[128]; } autologin_prompt_t;
typedef struct { int enabled; int stage; struct timespec t0, t_pass; long du_ms, dp_ms; char user[128]; char pass[128]; } autologin_blind_t;

static void autologin_try_prompt(autologin_prompt_t *al, const char *recent){
    if (!al->enabled || al->state>=2) return;
    if (al->state==0){
        if (istrstr(recent,"login:")||istrstr(recent,"user:")||istrstr(recent,"callsign:")){
            send_line_utf8_telnet_safe(al->user); al->state=1; return;
        }
    } else if (al->state==1){
        if (istrstr(recent,"password:")||istrstr(recent,"pass:")||istrstr(recent,"pw:")||istrstr(recent,"enter password")){
            send_line_utf8_telnet_safe(al->pass); al->state=2; return;
        }
    }
}
static void autologin_try_blind(autologin_blind_t *ab){
    if (!ab->enabled || ab->stage>=2) return;
    struct timespec now; clock_gettime(CLOCK_MONOTONIC,&now);
    long ms=since_ms(ab->t0, now);
    if (ab->stage==0 && ms>=ab->du_ms){ send_line_utf8_telnet_safe(ab->user); ab->stage=1; return; }
    if (ab->stage==1 && ms>=ab->dp_ms){ send_line_utf8_telnet_safe(ab->pass); ab->stage=2; ab->t_pass=now; return; }
}

/* Helper: stiamo seguendo la coda? */
static int is_following(void){
    int visible = rows-2; if (visible<1) visible=1;
    return (view_top + visible >= vis_count-1);
}

/* Echo locale (riga) nell'output */
static void local_echo_line(const wchar_t *src){
    int follow = is_following();
    size_t pfx = 2; /* "> " */
    size_t L = wcslen(src);
    wchar_t *echo = (wchar_t*)malloc(sizeof(wchar_t)*(pfx+L+1));
    if (echo){
        echo[0]=L'>'; echo[1]=L' '; wmemcpy(echo+2, src, L); echo[pfx+L]=L'\0';
        add_logical_line_w(echo, follow);
        free(echo);
        render_out();
    }
}

/* ---------- main ---------- */
int main(int argc, char **argv){
    signal(SIGPIPE, SIG_IGN);   /* non morire su write dopo chiusura peer */
    signal(SIGTSTP, SIG_IGN);   /* gestiamo ^Z manualmente (pass-thru) */

    if (argc<3){
        fprintf(stderr,"Uso: %s <host> <port> [-u USER -p PASS] [--blind-auto] [--cr-only] [--upper] [--no-auto-help] [--no-local-echo] [--no-pass-ctrl-z] [--ctrl-z-cr] [--unlock-delay MS] [--unlock-quiet MS]\n", argv[0]);
        return 1;
    }
    const char *host=argv[1], *port=argv[2];

    autologin_prompt_t alp; memset(&alp,0,sizeof alp);
    autologin_blind_t  alb; memset(&alb,0,sizeof alb);

    for (int i=3;i<argc;++i){
        if (!strcmp(argv[i],"-u") && i+1<argc){ strncpy(alp.user,argv[++i],sizeof(alp.user)-1); strncpy(alb.user,alp.user,sizeof(alb.user)-1); alp.enabled=1; }
        else if (!strcmp(argv[i],"-p") && i+1<argc){ strncpy(alp.pass,argv[++i],sizeof(alp.pass)-1); strncpy(alb.pass,alp.pass,sizeof(alb.pass)-1); alp.enabled=1; }
        else if (!strcmp(argv[i],"--blind-auto")){ alb.enabled=1; }
        else if (!strcmp(argv[i],"--cr-only")){ opt_cr_only=1; }
        else if (!strcmp(argv[i],"--upper")){ opt_upper=1; }
        else if (!strcmp(argv[i],"--no-auto-help")){ opt_auto_help=0; }
        else if (!strcmp(argv[i],"--no-local-echo")){ opt_local_echo=0; }
        else if (!strcmp(argv[i],"--no-pass-ctrl-z")){ opt_pass_ctrl_z=0; }
        else if (!strcmp(argv[i],"--ctrl-z-cr")){ opt_ctrlz_append_cr=1; }
        else if (!strcmp(argv[i],"--unlock-delay") && i+1<argc){ unlock_delay_ms=strtol(argv[++i],NULL,10); if (unlock_delay_ms<0) unlock_delay_ms=0; }
        else if (!strcmp(argv[i],"--unlock-quiet") && i+1<argc){ unlock_quiet_ms=strtol(argv[++i],NULL,10); if (unlock_quiet_ms<0) unlock_quiet_ms=0; }
        else { fprintf(stderr,"Opzione sconosciuta: %s\n", argv[i]); return 1; }
    }
    if ((alp.enabled||alb.enabled) && (alp.user[0]=='\0' || alp.pass[0]=='\0')){
        fprintf(stderr,"Autologin: servono sia -u che -p.\n"); return 1;
    }
    if (alb.enabled){ alb.du_ms=150; alb.dp_ms=1000; }

    signal(SIGWINCH, on_winch);
    ui_init();

    sockfd = connect_tcp(host, port);
    telnet_parser_t tp={0};

    /* Stato login/lock e recent */
    char recent[8192]; size_t rlen=0; recent[0]='\0';
    struct timespec last_rx; clock_gettime(CLOCK_MONOTONIC,&last_rx);
    int input_locked = (alp.enabled||alb.enabled) ? 1 : 0;
    int login_done_flag=0; struct timespec t_login_done; memset(&t_login_done,0,sizeof t_login_done);
    int auto_help_sent=0;
    if (alb.enabled) clock_gettime(CLOCK_MONOTONIC,&alb.t0);

    /* Input buffer (wide) */
    wchar_t ibuf[4096]; size_t ilen=0; ibuf[0]=L'\0';

    /* Primo render */
    render_out(); render_input(ibuf);

    for(;;){
        if (need_resize){
            endwin(); refresh(); clear(); getmaxyx(stdscr, rows, cols);
            ui_make_windows();
            int visible = rows-2; if (visible<1) visible=1;
            int keep_bottom = (view_top + visible >= vis_count-1);
            reflow(keep_bottom);
            render_out(); render_input(ibuf);
            need_resize=0;
        }

        /* Socket RX con piccolo timeout */
        fd_set rfds; FD_ZERO(&rfds); FD_SET(sockfd,&rfds);
        struct timeval tv={0,50000};
        int sr=select(sockfd+1,&rfds,NULL,NULL,&tv);
        if (sr<0 && errno!=EINTR) die_cleanup("select: %s", strerror(errno));

        if (alb.enabled && alb.stage<2) autologin_try_blind(&alb);

        if (sr>0 && FD_ISSET(sockfd,&rfds)){
            unsigned char in[4096], tmp[65536], out[65536];
            ssize_t n = read(sockfd, in, sizeof in);
            if (n==0) die_cleanup(NULL);
            if (n<0)  die_cleanup("read(sock): %s", strerror(errno));
            size_t o = telnet_filter_and_reply(&tp, in, (size_t)n, tmp, sizeof tmp);
            size_t m = normalize_incoming(tmp, o, out, sizeof out);

            if (m){
                /* Accumula nel buffer RX persistente */
                if (rx_len + m > rx_cap){
                    size_t newcap = (rx_cap==0? (m+1024) : rx_cap);
                    while (rx_len + m > newcap) newcap = newcap*2 + 1024;
                    char *nbuf = (char*)realloc(rx_acc, newcap);
                    if (!nbuf) die_cleanup("OOM RX");
                    rx_acc = nbuf; rx_cap = newcap;
                }
                memcpy(rx_acc + rx_len, out, m);
                rx_len += m;

                /* Estrai tutte le righe complete terminate da '\n' */
                size_t consumed = 0;
                for (;;){
                    void *pos = memchr(rx_acc + consumed, '\n', rx_len - consumed);
                    if (!pos) break;
                    size_t linelen = (char*)pos - (rx_acc + consumed);

                    /* Copia la riga (senza '\n') e processa */
                    char *line8 = (char*)malloc(linelen + 1);
                    if (!line8) die_cleanup("OOM line");
                    memcpy(line8, rx_acc + consumed, linelen);
                    line8[linelen] = '\0';

                    int visible = rows-2; if (visible<1) visible=1;
                    int follow = (view_top + visible >= vis_count-1);

                    wchar_t *w = utf8_to_wcs_lossy(line8);
                    if (w){
                        wchar_t *wt = expand_tabs_wcs(w, TABSTOP);
                        if (wt){ add_logical_line_w(wt, follow); free(wt); }
                        free(w);
                    }
                    free(line8);

                    consumed += linelen + 1; /* salta anche '\n' */
                }

                /* Sposta indietro l’eventuale coda parziale (senza '\n') */
                if (consumed > 0){
                    size_t rest = rx_len - consumed;
                    memmove(rx_acc, rx_acc + consumed, rest);
                    rx_len = rest;
                }

                clock_gettime(CLOCK_MONOTONIC,&last_rx);

                /* aggiorna recent (coda) */
                size_t chunk = m > sizeof(recent) ? sizeof(recent) : m;
                if (rlen + chunk > sizeof(recent)) {
                    size_t sh = (rlen + chunk) - sizeof(recent);
                    if (sh > rlen) sh = rlen;
                    memmove(recent, recent + sh, rlen - sh);
                    rlen -= sh;
                }
                memcpy(recent + rlen, out + (m - chunk), chunk); rlen += chunk;
                recent[(rlen<sizeof(recent))?rlen:sizeof(recent)-1] = '\0';

                if (alp.enabled && alp.state<2) {
                    autologin_try_prompt(&alp, recent);
                    if (alp.state==2){ login_done_flag=1; clock_gettime(CLOCK_MONOTONIC,&t_login_done); }
                }
                if (input_locked && (strstr(recent, "} ")||strstr(recent, "> ")||strstr(recent, "# ")||strstr(recent, ": ")||istrstr(recent,"connected to bbs"))){
                    struct timespec now; clock_gettime(CLOCK_MONOTONIC,&now);
                    if (since_ms(last_rx, now) >= unlock_quiet_ms) input_locked=0;
                }

                render_out(); render_input(ibuf);
            }
        }

        /* Sblocco input su timeout post-login */
        if (input_locked && (login_done_flag || alb.stage==2)){
            struct timespec now; clock_gettime(CLOCK_MONOTONIC,&now);
            struct timespec t0 = login_done_flag ? t_login_done : alb.t_pass;
            if (since_ms(t0, now) >= unlock_delay_ms) input_locked=0;
        }

        /* Auto "?" una volta sbloccato */
        if (!input_locked && !auto_help_sent && opt_auto_help){
            send_line_utf8_telnet_safe("?");
            auto_help_sent=1;
        }

        /* Tastiera (wide) */
        wint_t wch;
        int ch = get_wch(&wch);
        if (ch != ERR){
            if (wch == KEY_F(10) || wch == 3 /*Ctrl-C*/) die_cleanup(NULL);

            /* Ctrl-Z handling */
            else if (wch == 26
#ifdef KEY_SUSPEND
                     || wch == KEY_SUSPEND
#endif
            ){
                if (opt_pass_ctrl_z){
                    if (opt_local_echo) local_echo_line(L"^Z");
                    unsigned char sub = 0x1A;
                    write_telnet_safe(&sub, 1);
                    if (opt_ctrlz_append_cr) send_eol();
                } else {
                    /* sospensione UNIX standard */
                    endwin();
                    signal(SIGTSTP, SIG_DFL);
                    raise(SIGTSTP);    /* sospendi: riprende con 'fg' */

                    /* ripresa */
                    signal(SIGTSTP, SIG_IGN);
                    refresh(); clear(); getmaxyx(stdscr, rows, cols);
                    ui_make_windows();
                    int visible = rows-2; if (visible<1) visible=1;
                    int keep_bottom = (view_top + visible >= vis_count-1);
                    reflow(keep_bottom);
                    render_out(); render_input(ibuf);
                }
            }

            else if (wch == KEY_PPAGE){ int vis=rows-2; if (vis<1) vis=1; view_top -= vis/2; if (view_top<0) view_top=0; render_out(); render_input(ibuf); }
            else if (wch == KEY_NPAGE){ int vis=rows-2; if (vis<1) vis=1; view_top += vis/2; int max_top=vis_count-vis; if (max_top<0) max_top=0; if (view_top>max_top) view_top=max_top; render_out(); render_input(ibuf); }
            else if (wch == KEY_HOME){ view_top=0; render_out(); render_input(ibuf); }
            else if (wch == KEY_END){ int vis=rows-2; if (vis<1) vis=1; view_top = vis_count - vis; if (view_top<0) view_top=0; render_out(); render_input(ibuf); }
            else if (wch == KEY_UP){ if (view_top>0) view_top--; render_out(); render_input(ibuf); }
            else if (wch == KEY_DOWN){ int vis=rows-2; if (vis<1) vis=1; int max_top=vis_count-vis; if (max_top<0) max_top=0; if (view_top<max_top) view_top++; render_out(); render_input(ibuf); }
            else if (wch == '\n' || wch == '\r'){
                /* invio comando */
                ibuf[ilen]=L'\0';
                if (!input_locked){
                    /* upper opzionale */
                    wchar_t *tmp = NULL;
                    const wchar_t *src = ibuf;
                    if (opt_upper){
                        tmp = wcsdup(ibuf);
                        if (tmp){ for (size_t i=0; tmp[i]; ++i) tmp[i] = towupper(tmp[i]); src = tmp; }
                    }
                    /* ECHO LOCALE (wide) prima/insieme all'invio */
                    if (opt_local_echo){
                        local_echo_line(src);
                    }
                    /* wide -> utf8 e TX telnet-safe */
                    mbstate_t st; memset(&st,0,sizeof st);
                    size_t need = 4*wcslen(src) + 1;
                    char *out8 = (char*)malloc(need);
                    if (out8){
                        char *p = out8; size_t left = need;
                        for (size_t i=0; src[i]; ++i){
                            char buf[MB_CUR_MAX];
                            size_t r = wcrtomb(buf, src[i], &st);
                            if (r==(size_t)-1){ buf[0]='?'; r=1; memset(&st,0,sizeof st); }
                            if (r > left){ break; }
                            memcpy(p, buf, r); p += r; left -= r;
                        }
                        *p='\0';
                        write_telnet_safe((unsigned char*)out8, strlen(out8));
                        send_eol();
                        free(out8);
                    }
                    free(tmp);
                }
                ilen=0; ibuf[ilen]=L'\0'; render_input(ibuf);
            } else if (wch == KEY_BACKSPACE || wch == 127 || wch == 8){
                if (ilen>0) { ilen--; ibuf[ilen]=L'\0'; }
                render_input(ibuf);
            } else if (wch == KEY_DC){
                if (ilen>0) { ilen--; ibuf[ilen]=L'\0'; }
                render_input(ibuf);
            } else if (iswprint(wch)){
                if (ilen < (sizeof(ibuf)/sizeof(ibuf[0]))-1) ibuf[ilen++]=(wchar_t)wch, ibuf[ilen]=L'\0';
                render_input(ibuf);
            }
        }
    }
}

