
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdarg.h>
#include <malloc.h>
#include <dos.h>
#include <i86.h>
#include <bios.h>
#include <io.h>
#include <conio.h>
#include <fcntl.h>
#include <direct.h>
#include <sys/types.h>
#include <sys/stat.h>

static unsigned Pedir_Mem(unsigned paras, unsigned *seg) {
    union REGS r;
    r.h.ah = 0x48;
    r.x.bx = paras;
    int86(0x21, &r, &r);
    if (r.x.cflag) { *seg = r.x.bx; return r.x.ax; }
    *seg = r.x.ax;
    return 0;
}

static void soltar_Mem(unsigned seg) {
    union REGS r;
    struct SREGS sr;
    segread(&sr);
    sr.es = seg;
    r.h.ah = 0x49;
    int86x(0x21, &r, &r, &sr);
}

#define _dos_allocmem Pedir_Mem
#define _dos_freemem soltar_Mem

#define MAXF    1600
#define PROWS   17
#define PY      1
#define BROWS   (PROWS + 1)
#define PMAX    130

#define K_UP    0x4800
#define K_DOWN  0x5000
#define K_LEFT  0x4B00
#define K_RIGHT 0x4D00
#define K_PGUP  0x4900
#define K_PGDN  0x5100
#define K_HOME  0x4700
#define K_END   0x4F00
#define K_INS   0x5200
#define K_F3    0x3D00
#define K_F4    0x3E00
#define K_F5    0x3F00
#define K_F6    0x4000
#define K_F7    0x4100
#define K_F8    0x4200
#define K_F9    0x4300
#define K_F10   0x4400
#define K_AF1   0x6800
#define K_AF2   0x6900
#define K_TAB   0x0F09
#define K_ENTER 0x1C0D
#define K_CENT  0x1C0A
#define K_CTRLJ 0x240A
#define K_ESC   0x011B
#define K_BS    0x0E08
#define K_CTRLR 0x1312
#define K_CTRLO 0x180F
#define K_F1    0x3B00
#define K_F2    0x3C00
#define K_SF7   0x5A00
#define K_DEL   0x5300
#define K_CINS  0x9200
#define K_CHOME 0x7700
#define K_CEND  0x7500
#define K_CPGUP 0x8400
#define K_CPGDN 0x7600
#define K_CLEFT 0x7300
#define K_CRIGHT 0x7400
#define K_CTRLC 0x2E03
#define K_CTRLX 0x2D18
#define K_CTRLV 0x2F16
#define K_CTRLY 0x1519
#define K_CTRLI 0x1709
#define K_AF7   0x6E00
#define K_AF6   0x6D00
#define K_CF1   0x5E00
#define K_CF2   0x5F00
#define K_CTRLA 0x1E01
#define K_CTF3  0x6000
#define K_CTF4  0x6100
#define K_CTF5  0x6200
#define K_CTF6  0x6300
#define K_CTRLF 0x2106
#define K_CTRLD 0x2004
#define K_ALTC  0x2E00
#define K_CTRLP 0x1910

#define ATTR_ALL (_A_SUBDIR|_A_HIDDEN|_A_SYSTEM|_A_RDONLY|_A_ARCH)

typedef struct {
    char name[13];
    unsigned char attr;
    unsigned char sel;
    long size;
    unsigned date, tim;
} FENT;

typedef struct {
    char path[80];
    FENT *f;
    int n, cap, cur, top, x, nsel, brief, sort;
} PANEL;

typedef struct {
    char path[2][80];
    char cur[2][13];
    int top[2];
    int act;
    int brief[2];
    int sort[2];
} STATE;

#pragma pack(1)
typedef struct {
    char sig[4];
    unsigned char run, err, have, pad;
    char prog[80];
    unsigned char tail[128];
    union { STATE s; char raw[256]; } u;
} LSHARE;
#pragma pack()

enum { A_NORM, A_DIR, A_CUR, A_SEL, A_SELCUR, A_BORD, A_KEYN, A_KEYL,
       A_DLG, A_ERR, A_CMD, A_HEAD, A_SELD, A_HOT, A_SELHOT, A_INP, A_BTN, A_BTNF, A_ERSH, A_TXT, A_LCD, A_LCDD, A_LCDB };
static unsigned char colc[] = { 0x1B,0x1F,0x30,0x1E,0x3E,0x1B,0x07,0x30,0x30,0x4F,0x07,0x1E,0x0F,0x3E,0x0E,0x0F,0x70,0x2F,0x40,0x1F,0x0A,0x02,0x08 };
static unsigned char colm[] = { 0x07,0x0F,0x70,0x0F,0x70,0x07,0x07,0x70,0x70,0x70,0x07,0x0F,0x07,0x70,0x07,0x07,0x07,0x0F,0x70,0x07,0x0F,0x07,0x07 };
static unsigned char *col;

static PANEL pan[2];
static int act;
static char cmd[128];
static int cmdlen;
static unsigned short __far *vid;
static unsigned short __far *vreal;
static unsigned short *vbuf;
static int vbon, vdirty;
static unsigned short __far *usr;
static unsigned short __far *usrm;
static int mono;
static int ucx, ucy;
static LSHARE __far *lsh;
static char *iob;
static unsigned iobsz;
static char sp[PMAX], dp[PMAX];
static int ovall, abortf;
static int clockon, lastmin = -1;
static char qs[13];
static int qslen;
static char selm[41] = "*.*";
static STATE st;

static const char *mainkeys[10] = { "","Extras","View","Edit","Copy","Move","MkDir","Delete","Menu","Quit" };
static const char *altkeys[10] = { "DrvL","DrvR","","","","Rename","MkFile","","","" };
static int shownalt;
static const char *viewkeys[10] = { "","","Quit","Hex/Txt","","","Find","","","Quit" };

static int formato_V(char *o, const char *f, va_list ap) {
    static const char hx[] = "0123456789ABCDEF";
    char *o0 = o, tmp[12], *p;
    int left, zero, w, prec, lng, n, neg, base;
    unsigned long v;
    long l;

    while (*f)
    {
        if (*f != '%') { *o++ = *f++; continue; }
        f++;
        left = zero = lng = neg = 0;
        w = 0; prec = -1; base = 10;
        if (*f == '-') { left = 1; f++; }
        if (*f == '0') { zero = 1; f++; }
        while (*f >= '0' && *f <= '9') w = w * 10 + *f++ - '0';
        if (*f == '.') {
            f++; prec = 0;
            while (*f >= '0' && *f <= '9') prec = prec * 10 + *f++ - '0';
        }
        if (*f == 'l') { lng = 1; f++; }
        p = tmp; n = 0;
        switch (*f++) {
        case 's':
            p = va_arg(ap, char *);
            n = strlen(p);
            if (prec >= 0 && n > prec) n = prec;
            break;
        case 'c':
            tmp[0] = (char)va_arg(ap, int);
            n = 1;
            break;
        case 'd':
            l = lng ? va_arg(ap, long) : (long)va_arg(ap, int);
            if (l < 0) { neg = 1; v = (unsigned long)(-l); } else v = (unsigned long)l;
            goto num;
        case 'X':
            base = 16;

        case 'u':
            v = lng ? va_arg(ap, unsigned long) : (unsigned long)va_arg(ap, unsigned);
        num:
            p = tmp + 11; *p = 0;
            do { *--p = hx[(int)(v % base)]; v /= base; } while (v);
            if (neg) *--p = '-';
            n = tmp + 11 - p;
            break;
        case '%':
            tmp[0] = '%'; n = 1;
            break;
        default:
            break;
        }
        w -= n;
        if (!left) while (w > 0) { *o++ = zero ? '0' : ' '; w--; }
        while (n--) *o++ = *p++;
        while (w > 0) { *o++ = ' '; w--; }
    }
    *o = 0;
    return o - o0;
}

static int fmt(char *o, const char *f, ...) {
    va_list ap;
    int n;
    va_start(ap, f);
    n = formato_V(o, f, ap);
    va_end(ap);
    return n;
}

static void Poner_dos(const char *s) {
    write(1, s, strlen(s));
}

static int __far error_Disco(unsigned deverr, unsigned errcode, unsigned __far *devhdr)
{
    (void)deverr; (void)errcode; (void)devhdr;
    return _HARDERR_FAIL;
}

static void __interrupt __far Sin_Ctrlc(void)
{
}

static void Dib_reloj(int force);
static void Dib_Teclas(const char **lab);
static void Volcar(void);

static unsigned lastraw;

static void vaciar_teclas(void)
{
    while (_bios_keybrd(_KEYBRD_READY) == lastraw) _bios_keybrd(_KEYBRD_READ);
}

static void Repro_cd(void);
static void Calc_flotante(void);
static int incd, incalc;

static unsigned short popbuf[56 * 21];
static unsigned long cdts_s[100];
static unsigned char cdtc_s[100];

static unsigned Norm_Tecla(unsigned k) {
    if ((k & 0xFF) == 0xE0 && (k >> 8)) k &= 0xFF00;
    else if ((k & 0xFF) == 0) k &= 0xFF00;
    if ((k >> 8) == 0xE0) k = 0x1C00 | (k & 0xFF);
    return k;
}

static unsigned Leer_Tecla(void) {
    unsigned k;
    unsigned __far *tick = (unsigned __far *)MK_FP(0x40, 0x6C);
    unsigned last = *tick;
    for (;;) {
        if (vbon && !_bios_keybrd(_KEYBRD_READY)) Volcar();
        while (!_bios_keybrd(_KEYBRD_READY))
        {
            if (clockon && *tick - last >= 18) { last = *tick; Dib_reloj(0); Volcar(); }
            if (clockon) {
                int al = (*(unsigned char __far *)MK_FP(0x40, 0x17) & 8) != 0;
                if (al != shownalt) { Dib_Teclas(al ? altkeys : mainkeys); Volcar(); }
            }
        }
        k = _bios_keybrd(_KEYBRD_READ);
        lastraw = k;
        k = Norm_Tecla(k);

        if (k == K_CTRLP && !incd && !incalc) { Repro_cd(); continue; }

        if ((k == K_ALTC || k == K_CTRLC) && !clockon && !incd) { Calc_flotante(); continue; }
        return k;
    }
}

static int hay_Esc(void) {
    if (_bios_keybrd(_KEYBRD_READY))
    {
        if ((_bios_keybrd(_KEYBRD_READ) & 0xFF) == 27) return 1;
    }
    return 0;
}

static void pos_cursor(int x, int y)
{
    union REGS r;
    r.h.ah = 2; r.h.bh = 0; r.h.dh = y; r.h.dl = x;
    int86(0x10, &r, &r);
}

static void Forma_cursor(int on) {
    union REGS r;
    r.h.ah = 1;
    r.x.cx = on ? (mono ? 0x0B0C : 0x0607) : 0x2000;
    int86(0x10, &r, &r);
}

static void Ini_Video(void)
{
    union REGS r;
    r.h.ah = 0x0F;
    int86(0x10, &r, &r);
    if (r.h.al == 7) {
        mono = 1;
        vid = (unsigned short __far *)MK_FP(0xB000, 0);

        if (!usrm) usrm = (unsigned short __far *)_fmalloc(4000);
        usr = usrm;
    } else {
        mono = 0;
        vid = (unsigned short __far *)MK_FP(0xB800, 0);
        if (r.h.al != 2 && r.h.al != 3) {
            r.x.ax = 3;
            int86(0x10, &r, &r);
        }

        usr = (unsigned short __far *)MK_FP(0xB800, 0x1000);
    }
    col = mono ? colm : colc;
}

static void Guardar_pant(void)
{
    union REGS r;
    int i;
    if (usr) for (i = 0; i < 2000; i++) usr[i] = vid[i];
    r.h.ah = 3; r.h.bh = 0;
    int86(0x10, &r, &r);
    ucx = r.h.dl; ucy = r.h.dh;
}

static void Ver_Pant_dos(void) {
    int i;
    unsigned short __far *rv = vbon ? vreal : vid;
    if (usr) for (i = 0; i < 2000; i++) rv[i] = usr[i];
    pos_cursor(ucx, ucy);
}

static void Ini_Buffer(void)
{
    if (vbon) return;
    vbuf = (unsigned short *)malloc(4000);
    if (!vbuf) return;
    vreal = vid;
    _fmemcpy((void __far *)vbuf, vreal, 4000);
    vid = (unsigned short __far *)vbuf;
    vbon = 1;
    vdirty = 0;
}

static void Volcar(void)
{
    unsigned st;
    if (!vbon || !vdirty) return;
    vdirty = 0;
    if (!mono) {
        st = 0x3DA;
        while (inp(st) & 8) ;
        while (!(inp(st) & 8)) ;
    }
    _fmemcpy(vreal, (void __far *)vbuf, 4000);
}

static void volcar_rapido(void) {
    if (!vbon || !vdirty) return;
    vdirty = 0;
    _fmemcpy(vreal, (void __far *)vbuf, 4000);
}

static void Fin_buffer(void) {
    if (!vbon) return;
    Volcar();
    vid = vreal;
    free(vbuf);
    vbon = 0;
}

static void poner_car(int x, int y, int a, int c) {
    vdirty = 1;
    vid[y * 80 + x] = ((unsigned)col[a] << 8) | (unsigned char)c;
}

static void linea_H(int x, int y, int w, int a, int c) {
    unsigned short __far *p = vid + y * 80 + x;
    unsigned v = ((unsigned)col[a] << 8) | (unsigned char)c;
    vdirty = 1;
    while (w-- > 0) *p++ = v;
}

static void poner_Txt(int x, int y, int a, const char *s, int w) {
    unsigned short __far *p = vid + y * 80 + x;
    unsigned at = (unsigned)col[a] << 8;
    vdirty = 1;
    while (w > 0 && *s) { *p++ = at | (unsigned char)*s++; w--; }
    while (w > 0) { *p++ = at | ' '; w--; }
}

static void Caja(int x, int y, int w, int h, int a, const char *title)
{
    int i;
    char t[70];
    poner_car(x, y, a, 0xC9); linea_H(x + 1, y, w - 2, a, 0xCD); poner_car(x + w - 1, y, a, 0xBB);
    for (i = 1; i < h - 1; i++) {
        poner_car(x, y + i, a, 0xBA); linea_H(x + 1, y + i, w - 2, a, ' '); poner_car(x + w - 1, y + i, a, 0xBA);
    }
    poner_car(x, y + h - 1, a, 0xC8); linea_H(x + 1, y + h - 1, w - 2, a, 0xCD); poner_car(x + w - 1, y + h - 1, a, 0xBC);
    if (title && *title) {
        i = fmt(t, " %.60s ", title);
        poner_Txt(x + (w - i) / 2, y, a, t, i);
    }
    vdirty = 1;

    if (x + w + 2 <= 80 && y + h < 24) {
        unsigned short __far *p;
        unsigned sa = (unsigned)(mono ? 0x07 : 0x08) << 8;
        for (i = 1; i <= h; i++) {
            p = vid + (y + i) * 80 + x + w;
            p[0] = sa | (unsigned char)p[0];
            p[1] = sa | (unsigned char)p[1];
        }
        p = vid + (y + h) * 80 + x + 2;
        for (i = 0; i < w - 2; i++) p[i] = sa | (unsigned char)p[i];
    }
}

static void poner_Hot(int x, int y, int a, int ah, const char *s, int w) {
    int i = 0;
    poner_Txt(x, y, a, s, w);
    while (s[i] == ' ') i++;
    if (s[i] && i < w) poner_car(x + i, y, ah, s[i]);
}

static void Boton(int x, int y, const char *s, int focus, int sh)
{
    int l = strlen(s);
    poner_Txt(x, y, focus ? A_BTNF : A_BTN, s, l);
    poner_car(x + l, y, sh, 0xDC);
    linea_H(x + 1, y + 1, l, sh, 0xDF);
}
#define button(x, y, s, f) Boton(x, y, s, f, A_DLG)

static void Dib_Teclas(const char **lab)
{
    int i;
    char n[4];
    shownalt = (lab == altkeys);
    for (i = 0; i < 10; i++) {
        fmt(n, "%2d", i + 1);
        poner_Txt(i * 8, 24, A_KEYN, n, 2);
        poner_Txt(i * 8 + 2, 24, A_KEYL, lab[i], 6);
    }
}

static void Aviso(const char *title, const char *text)
{
    Caja(10, 9, 60, 6, A_ERR, title);
    poner_Txt(12, 10, A_ERR, text, 56);
    Boton(37, 12, "  Ok  ", 1, A_ERSH);
    Forma_cursor(0);
    Leer_Tecla();
    Forma_cursor(1);
}

static int pedir_tecla(const char *title, const char *l1, const char *l2, const char *keys) {
    const char *lb[4];
    int ks[4], n = 0, i, f = 0, x, tot = 0, c;
    unsigned k;
    (void)l2;
    for (i = 0; keys[i] && n < 3; i++, n++) {
        ks[n] = keys[i];
        lb[n] = keys[i] == 'Y' ? "  Yes   " : keys[i] == 'N' ? "   No   " : "  All   ";
    }
    ks[n] = 27; lb[n] = " Cancel "; n++;
    for (i = 0; i < n; i++) tot += strlen(lb[i]) + 2;
    Forma_cursor(0);
    for (;;)
    {
        Caja(10, 9, 60, 6, A_DLG, title);
        poner_Txt(12, 10, A_DLG, l1, 56);
        x = 10 + (60 - tot) / 2;
        for (i = 0; i < n; i++) {
            button(x, 12, lb[i], i == f);
            x += strlen(lb[i]) + 2;
        }
        k = Leer_Tecla();
        c = k & 0xFF;
        if (c == 27) { c = 27; break; }
        if (c == 13) { c = ks[f]; break; }
        if (k == K_LEFT) f = (f + n - 1) % n;
        else if (k == K_RIGHT || c == 9) f = (f + 1) % n;
        else {
            c = toupper(c);
            if (c && strchr(keys, c)) break;
        }
    }
    Forma_cursor(1);
    return c;
}

static int confirmar(const char *title, const char *text) {
    return pedir_tecla(title, text, "", "YN") == 'Y';
}

static void status(const char *title, const char *text)
{
    Caja(10, 10, 60, 4, A_DLG, title);
    poner_Txt(12, 11, A_DLG, text, 56);
    poner_Txt(12, 12, A_DLG, "Esc = cancel", 56);
    volcar_rapido();
}

static int ibhome;
static int ibfresh;

static int pedir_Texto(const char *title, const char *prompt, char *buf, int max)
{
    int l = strlen(buf), cp = ibhome ? 0 : l, off, c, fresh = ibfresh;
    unsigned k;
    ibfresh = 0; ibhome = 0;
    for (;;) {
        Caja(10, 9, 60, 7, A_DLG, title);
        poner_Txt(12, 10, A_DLG, prompt, 56);
        off = cp > 53 ? cp - 53 : 0;
        poner_car(12, 11, A_DLG, '[');
        poner_Txt(13, 11, fresh ? A_SELD : A_INP, buf + off, 54);
        poner_car(67, 11, A_DLG, ']');
        button(23, 13, "  Ok  ", 1);
        button(39, 13, " Cancel ", 0);
        pos_cursor(13 + cp - off, 11);
        k = Leer_Tecla();
        c = k & 0xFF;
        if (fresh && c >= 32 && c != '\\') { l = cp = 0; buf[0] = 0; }
        if (c >= 32 || k == K_LEFT || k == K_RIGHT || k == K_HOME || k == K_END || k == K_DEL || c == 8) fresh = 0;
        if (k == K_LEFT) { if (cp) cp--; }
        else if (k == K_RIGHT) { if (cp < l) cp++; }
        else if (k == K_HOME) cp = 0;
        else if (k == K_END) cp = l;
        else if (k == K_DEL) {
            if (cp < l) { memmove(buf + cp, buf + cp + 1, l - cp); l--; }
        }
        else if (c == 13) return 1;
        else if (c == 27) return 0;
        else if (c == 8) {
            if (cp) { memmove(buf + cp - 1, buf + cp, l - cp + 1); cp--; l--; }
        }
        else if (c >= 32 && l < max) {
            memmove(buf + cp + 1, buf + cp, l - cp + 1);
            buf[cp++] = (char)c;
            l++;
        }
    }
}

static void unir_ruta(char *o, const char *dir, const char *name)
{
    int l;
    strcpy(o, dir);
    l = strlen(o);
    if (l && o[l - 1] != '\\') strcat(o, "\\");
    strcat(o, name);
}

static void ruta_Abs(char *o, const char *base, const char *in)
{
    int l;
    if (in[0] && in[1] == ':') strcpy(o, in);
    else if (in[0] == '\\') { o[0] = base[0]; o[1] = ':'; strcpy(o + 2, in); }
    else unir_ruta(o, base, in);
    strupr(o);
    l = strlen(o);
    if (l == 2) strcat(o, "\\");
    else if (l > 3 && o[l - 1] == '\\') o[l - 1] = 0;
}

static int poner_unidad(int c) {
    unsigned d = toupper(c) - 'A' + 1, n, cur;
    _dos_setdrive(d, &n);
    _dos_getdrive(&cur);
    return cur != d;
}

static void Poner_dir(const char *path) {
    poner_unidad(path[0]);
    chdir(path);
}

static int Es_dir(const char *path) {
    struct find_t ft;
    int l = strlen(path);
    if (l == 3 && path[1] == ':' && path[2] == '\\') return 1;
    if (_dos_findfirst(path, _A_SUBDIR | _A_HIDDEN | _A_SYSTEM, &ft)) return 0;
    return (ft.attrib & _A_SUBDIR) != 0;
}

static int existe(const char *path)
{
    struct find_t ft;
    return _dos_findfirst(path, _A_HIDDEN | _A_SYSTEM | _A_RDONLY, &ft) == 0;
}

static int es_exe(const char *n) {
    const char *e = strrchr(n, '.');
    if (!e) return 0;
    return !stricmp(e, ".EXE") || !stricmp(e, ".COM") || !stricmp(e, ".BAT");
}

static int Coincide(const char *p, const char *s) {
    for (;;)
    {
        if (*p == '*') {
            p++;
            if (!*p) return 1;
            do { if (Coincide(p, s)) return 1; } while (*s++);
            return 0;
        }
        if (!*p) return !*s;
        if (!*s) return 0;
        if (*p != '?' && toupper(*p) != toupper(*s)) return 0;
        p++; s++;
    }
}

static int Coincide_mascara(const char *mask, const char *name) {
    char one[41], nm[14];
    int i;
    strcpy(nm, name);
    if (!strchr(nm, '.')) strcat(nm, ".");
    while (*mask)
    {
        while (*mask == ' ' || *mask == ',' || *mask == ';') mask++;
        i = 0;
        while (*mask && *mask != ' ' && *mask != ',' && *mask != ';' && i < 40) one[i++] = *mask++;
        one[i] = 0;
        if (i && Coincide(one, nm)) return 1;
    }
    return 0;
}

static int cursort;

static int Ordenar_fichas(const void *a, const void *b) {
    const FENT *x = (const FENT *)a, *y = (const FENT *)b;
    int dx = (x->attr & _A_SUBDIR) != 0, dy = (y->attr & _A_SUBDIR) != 0, r;
    const char *ex, *ey;
    if (x->name[0] == '.' && !strcmp(x->name, "..")) return -1;
    if (y->name[0] == '.' && !strcmp(y->name, "..")) return 1;
    if (dx != dy) return dy - dx;
    if (!dx) {
        if (cursort == 1) {
            ex = strrchr(x->name, '.'); ey = strrchr(y->name, '.');
            r = strcmp(ex ? ex + 1 : "", ey ? ey + 1 : "");
            if (r) return r;
        } else if (cursort == 2) {
            if (x->date != y->date) return y->date > x->date ? 1 : -1;
            if (x->tim != y->tim) return y->tim > x->tim ? 1 : -1;
        } else if (cursort == 3) {
            if (x->size != y->size) return y->size > x->size ? 1 : -1;
        }
    }
    return strcmp(x->name, y->name);
}

static int Leer_Dir(PANEL *p) {
    struct find_t ft;
    char pat[90];
    unsigned rc;
    FENT *e;

    unir_ruta(pat, p->path, "*.*");
    rc = _dos_findfirst(pat, ATTR_ALL, &ft);
    if (rc && rc != 2 && rc != 0x12) return -1;
    free(p->f);
    p->f = NULL; p->cap = 0; p->n = 0; p->nsel = 0;
    while (!rc) {
        if (strcmp(ft.name, "."))
        {
            if (p->n == p->cap) {
                if (p->cap >= MAXF) break;
                e = (FENT *)realloc(p->f, (p->cap + 64) * sizeof(FENT));
                if (!e) break;
                p->f = e;
                p->cap += 64;
            }
            e = &p->f[p->n++];
            strcpy(e->name, ft.name);
            if (!(ft.attrib & _A_SUBDIR)) strlwr(e->name);
            e->attr = ft.attrib;
            e->sel = 0;
            e->size = ft.size;
            e->date = ft.wr_date;
            e->tim = ft.wr_time;
        }
        rc = _dos_findnext(&ft);
    }
    cursort = p->sort;
    if (p->n > 1) qsort(p->f, p->n, sizeof(FENT), Ordenar_fichas);
    return 0;
}

static void Ajustar_vista(PANEL *p);
static void Buscar_Cursor(PANEL *p, const char *nm);

static void Reordenar(PANEL *p) {
    char nm[13];
    nm[0] = 0;
    if (p->n) strcpy(nm, p->f[p->cur].name);
    cursort = p->sort;
    if (p->n > 1) qsort(p->f, p->n, sizeof(FENT), Ordenar_fichas);
    Buscar_Cursor(p, nm);
}

static void Ajustar_vista(PANEL *p) {
    if (p->cur >= p->n) p->cur = p->n - 1;
    if (p->cur < 0) p->cur = 0;
    if (p->brief)
    {
        if (p->cur < p->top) p->top = p->cur / BROWS * BROWS;
        if (p->cur >= p->top + 3 * BROWS) p->top = (p->cur / BROWS - 2) * BROWS;
        if (p->top < 0) p->top = 0;
        p->top = p->top / BROWS * BROWS;
        return;
    }
    if (p->top > p->cur) p->top = p->cur;
    if (p->cur >= p->top + PROWS) p->top = p->cur - PROWS + 1;
    if (p->top < 0) p->top = 0;
}

static void Buscar_Cursor(PANEL *p, const char *nm)
{
    int i;
    for (i = 0; i < p->n; i++)
        if (!stricmp(p->f[i].name, nm)) { p->cur = i; break; }
    Ajustar_vista(p);
}

static void recontar(PANEL *p) {
    int i;
    p->nsel = 0;
    for (i = 0; i < p->n; i++) if (p->f[i].sel) p->nsel++;
}

static void Quitar_Dir(char *path, char *nm)
{
    char *s = strrchr(path, '\\');
    if (nm) nm[0] = 0;
    if (!s) return;
    if (nm) { strncpy(nm, s + 1, 12); nm[12] = 0; }
    if (s - path == 2) s[1] = 0; else *s = 0;
}

static void refrescar(int i)
{
    PANEL *p = &pan[i];
    char nm[13];
    nm[0] = 0;
    if (p->n) strcpy(nm, p->f[p->cur].name);
    while (Leer_Dir(p))
    {
        if (strlen(p->path) <= 3) { p->n = 0; break; }
        Quitar_Dir(p->path, NULL);
    }
    Buscar_Cursor(p, nm);
}

static int cambiar_panel(PANEL *p, const char *np, const char *sel)
{
    char old[80];
    strcpy(old, p->path);
    strcpy(p->path, np);
    if (Leer_Dir(p)) {
        strcpy(p->path, old);
        Leer_Dir(p);
        Ajustar_vista(p);
        Aviso("Error", "Cannot read directory");
        return -1;
    }
    p->cur = 0; p->top = 0;
    if (sel) Buscar_Cursor(p, sel);
    return 0;
}

static void ir_A_Dir(int i, const char *arg)
{
    PANEL *p = &pan[i];
    char np[90];
    Poner_dir(p->path);
    if (arg[0] && arg[1] == ':') {
        if (poner_unidad(arg[0])) { Aviso("Error", "Invalid drive"); return; }
        arg += 2;
    }
    if (*arg && chdir(arg)) { Aviso("Error", "Directory not found"); return; }
    if (!getcwd(np, 80)) { Aviso("Error", "Drive not ready"); return; }
    cambiar_panel(p, np, NULL);
}

static void Dib_fila(PANEL *p, int i, int r)
{
    FENT *e;
    int k, a;
    char b[90], nm[13], sz[16];
        k = p->top + r;
        if (k < p->n)
        {
            e = &p->f[k];

            memset(nm, ' ', 12); nm[12] = 0;
            if (e->name[0] == '.') memcpy(nm, e->name, strlen(e->name));
            else
            {
                const char *s = e->name;
                int j = 0;
                while (*s && *s != '.' && j < 8) nm[j++] = *s++;
                if (*s == '.') { s++; j = 9; while (*s && j < 12) nm[j++] = *s++; }
            }
            if (!strcmp(e->name, "..")) fmt(sz, " %cUP--DIR%c", 0x10, 0x11);
            else if (e->attr & _A_SUBDIR) fmt(sz, " %cSUB-DIR%c", 0x10, 0x11);
            else fmt(sz, "%10ld", e->size);
            fmt(b, "%s%c%s%c%02u-%02u-%02u%c%02u:%02u", nm, 0xB3, sz, 0xB3,
                e->date & 31, (e->date >> 5) & 15, ((e->date >> 9) + 80) % 100, 0xB3,
                e->tim >> 11, (e->tim >> 5) & 63);
            a = e->sel ? A_SEL : ((e->attr & _A_SUBDIR) ? A_DIR : A_NORM);
            if (i == act && k == p->cur) a = e->sel ? A_SELCUR : A_CUR;
        } else {
            fmt(b, "%12s%c%10s%c%8s%c%5s", "", 0xB3, "", 0xB3, "", 0xB3, "");
            a = A_NORM;
        }
        poner_Txt(p->x + 1, PY + 2 + r, a, b, 38);
}

static void dib_Info(PANEL *p) {
    FENT *e;
    int x = p->x, r = PY + 3 + PROWS, k;
    char b[90];
    unsigned long sb;
    if (p->nsel)
    {
        sb = 0;
        for (k = 0; k < p->n; k++) if (p->f[k].sel) sb += p->f[k].size;
        k = fmt(b, "%lu bytes in %d sel.", sb, p->nsel);
        if (k > 38) k = 38;
        poner_Txt(x + 1, r, A_SEL, "", 38);
        poner_Txt(x + 1 + (38 - k) / 2, r, A_SEL, b, k);
    } else if (p->n) {
        e = &p->f[p->cur];
        if (p->brief)
        {
            if (e->attr & _A_SUBDIR) fmt(b, "%-12s %10s %02u-%02u-%02u %02u:%02u", e->name, "<DIR>",
                e->date & 31, (e->date >> 5) & 15, ((e->date >> 9) + 80) % 100, e->tim >> 11, (e->tim >> 5) & 63);
            else fmt(b, "%-12s %10ld %02u-%02u-%02u %02u:%02u", e->name, e->size,
                e->date & 31, (e->date >> 5) & 15, ((e->date >> 9) + 80) % 100, e->tim >> 11, (e->tim >> 5) & 63);
        }
        else if (e->attr & _A_SUBDIR) fmt(b, "%-13s<DIR>", e->name);
        else fmt(b, "%-13s%ld", e->name, e->size);
        poner_Txt(x + 1, r, A_NORM, b, 38);
    } else poner_Txt(x + 1, r, A_NORM, "", 38);
}

static void Dib_Panel(int i) {
    PANEL *p = &pan[i];
    FENT *e;
    int x = p->x, r, k, a;
    char b[90], nm[13], sz[16];
    const char *t;
    unsigned long sb;

    poner_car(x, PY, A_BORD, 0xC9); linea_H(x + 1, PY, 38, A_BORD, 0xCD); poner_car(x + 39, PY, A_BORD, 0xBB);
    k = strlen(p->path);
    t = p->path;
    if (k > 34) { t += k - 34; k = 34; }
    fmt(b, " %s ", t);
    poner_Txt(x + (40 - (k + 2)) / 2, PY, i == act ? A_CUR : A_BORD, b, k + 2);
    for (r = PY + 1; r < PY + PROWS + 4; r++) { poner_car(x, r, A_BORD, 0xBA); poner_car(x + 39, r, A_BORD, 0xBA); }

    if (!p->brief)
    {
        fmt(b, "   Name     %c  Bytes   %c  Date   %cTime ", 0xB3, 0xB3, 0xB3);
        poner_Txt(x + 1, PY + 1, A_HEAD, b, 38);
    }

    for (r = 0; r < BROWS && p->brief; r++) {
        int cl;
        for (cl = 0; cl < 3; cl++) {
            k = p->top + cl * BROWS + r;
            if (k < p->n) {
                e = &p->f[k];
                memset(nm, ' ', 12); nm[12] = 0;
                if (e->name[0] == '.') memcpy(nm, e->name, strlen(e->name));
                else {
                    const char *s2 = e->name;
                    int j = 0;
                    while (*s2 && *s2 != '.' && j < 8) nm[j++] = *s2++;
                    if (*s2 == '.') { s2++; j = 9; while (*s2 && j < 12) nm[j++] = *s2++; }
                }
                a = e->sel ? A_SEL : ((e->attr & _A_SUBDIR) ? A_DIR : A_NORM);
                if (i == act && k == p->cur) a = e->sel ? A_SELCUR : A_CUR;
            } else { memset(nm, ' ', 12); nm[12] = 0; a = A_NORM; }
            poner_Txt(x + 1 + cl * 13, PY + 1 + r, a, nm, 12);
            if (cl < 2) poner_car(x + 13 + cl * 13, PY + 1 + r, A_NORM, 0xB3);
        }
    }
    for (r = 0; r < PROWS && !p->brief; r++) Dib_fila(p, i, r);

    r = PY + 2 + PROWS;
    poner_car(x, r, A_BORD, 0xC7); linea_H(x + 1, r, 38, A_BORD, 0xC4); poner_car(x + 39, r, A_BORD, 0xB6);
    if (p->brief) { poner_car(x + 13, r, A_BORD, 0xC1); poner_car(x + 26, r, A_BORD, 0xC1); }
    else { poner_car(x + 13, r, A_BORD, 0xC1); poner_car(x + 24, r, A_BORD, 0xC1); poner_car(x + 33, r, A_BORD, 0xC1); }
    r++;

    dib_Info(p);
    r++;

    poner_car(x, r, A_BORD, 0xC8); linea_H(x + 1, r, 38, A_BORD, 0xCD); poner_car(x + 39, r, A_BORD, 0xBC);
}

static int dtop[2], dcur[2];
static int needfull = 1, moved;

static void Dib_Rapido(void)
{
    PANEL *p = &pan[act];
    int i = act, d = p->top - dtop[i], r, x = p->x + 1;
    int rows[3], nr = 0, j;

    if (p->brief || d > 1 || d < -1) Dib_Panel(i);
    else {
        if (d == 1) {
            for (r = 0; r < PROWS - 1; r++)
                _fmemmove(vid + (PY + 2 + r) * 80 + x, vid + (PY + 3 + r) * 80 + x, 76);
            rows[nr++] = PROWS - 1;
        } else if (d == -1) {
            for (r = PROWS - 1; r > 0; r--)
                _fmemmove(vid + (PY + 2 + r) * 80 + x, vid + (PY + 1 + r) * 80 + x, 76);
            rows[nr++] = 0;
        }
        rows[nr++] = dcur[i] - p->top;
        rows[nr++] = p->cur - p->top;
        for (j = 0; j < nr; j++)
            if (rows[j] >= 0 && rows[j] < PROWS) Dib_fila(p, i, rows[j]);
        dib_Info(p);
        vdirty = 1;
    }
    dtop[i] = p->top; dcur[i] = p->cur;
}

static void Marcar_Dibujado(void) {
    dtop[0] = pan[0].top; dcur[0] = pan[0].cur;
    dtop[1] = pan[1].top; dcur[1] = pan[1].cur;
    needfull = 0; moved = 0;
}

static void Dib_Linea_Cmd(void)
{
    char b[220];
    int l, o;
    l = fmt(b, "%s>%s", pan[act].path, cmd);
    o = l > 79 ? l - 79 : 0;
    poner_Txt(0, 23, A_CMD, b + o, 80);
    pos_cursor(l - o, 23);
}

#define NMENU 6
static const char *mtitle[NMENU] = { "Left", "Files", "Commands", "Options", "Utils", "Right" };
static const int mpos[NMENU] = { 2, 10, 19, 31, 42, 51 };

static void Dib_reloj(int force) {
    struct dostime_t t;
    char b[8];
    _dos_gettime(&t);
    if (!force && t.minute == lastmin) return;
    lastmin = t.minute;
    fmt(b, "%2d:%02d", t.hour, t.minute);
    poner_Txt(74, 0, A_KEYL, b, 6);
}

static void dib_menu(void) {
    int i;
    poner_Txt(0, 0, A_KEYL, "  Left    Files    Commands    Options    Utils    Right", 74);
    for (i = 0; i < NMENU; i++) poner_car(mpos[i], 0, A_HOT, mtitle[i][0]);
    Dib_reloj(1);
}

static void dib_todo(void) {
    dib_menu();
    Dib_Panel(0);
    Dib_Panel(1);
    Dib_Linea_Cmd();
    Dib_Teclas(mainkeys);
}

static void sel_mascara(PANEL *p, const char *mask, int on)
{
    int i;
    for (i = 0; i < p->n; i++) {
        if (!strcmp(p->f[i].name, "..")) continue;
        if (Coincide_mascara(mask, p->f[i].name)) p->f[i].sel = (unsigned char)on;
    }
    recontar(p);
}

static void Sel_solo(PANEL *p, int dirs) {
    int i, d;
    for (i = 0; i < p->n; i++) {
        if (!strcmp(p->f[i].name, "..")) continue;
        d = (p->f[i].attr & _A_SUBDIR) != 0;
        p->f[i].sel = (unsigned char)(d == dirs);
    }
    recontar(p);
}

static void hacer_sel(int on) {
    if (!pedir_Texto(on ? "Select" : "Unselect", "Mask (e.g. *.* *.TXT):", selm, 40)) return;
    if (selm[0]) sel_mascara(&pan[act], selm, on);
}

static void invertir_Sel(PANEL *p) {
    int i;
    for (i = 0; i < p->n; i++) {
        if (!strcmp(p->f[i].name, "..") || (p->f[i].attr & _A_SUBDIR)) continue;
        p->f[i].sel ^= 1;
    }
    recontar(p);
}

static void Hacer_Atrib(void)
{
    static const unsigned fl[4] = { _A_RDONLY, _A_ARCH, _A_HIDDEN, _A_SYSTEM };
    static const char *nmz[4] = { "Read-only", "Archive", "Hidden", "System" };
    PANEL *p = &pan[act];
    FENT *e;
    unsigned at = 0, na, old;
    int on[4], f = 0, i, nf = 0, ok = 0;
    unsigned k;
    char path[100], b[40];

    if (!p->n) return;
    for (i = 0; i < p->n; i++) if (p->nsel ? p->f[i].sel : (i == p->cur)) {
        if (!strcmp(p->f[i].name, "..")) continue;
        if (!nf) at = p->f[i].attr;
        nf++;
    }
    if (!nf) return;
    for (i = 0; i < 4; i++) on[i] = (at & fl[i]) != 0;
    Forma_cursor(0);
    for (;;)
    {
        Caja(25, 7, 30, 11, A_DLG, "Attributes");
        if (nf > 1) fmt(b, "%d files", nf); else fmt(b, "%.12s", p->f[p->cur].name);
        poner_Txt(27, 8, A_DLG, b, 26);
        for (i = 0; i < 4; i++) {
            fmt(b, "[%c] %s", on[i] ? 'x' : ' ', nmz[i]);
            poner_Hot(28, 10 + i, i == f ? A_SELD : A_DLG, i == f ? A_SELHOT : A_HOT, b + 0, 22);
        }
        button(29, 15, "  Ok  ", 0);
        button(41, 15, " Cancel ", 0);
        k = Leer_Tecla();
        if (k == K_ESC) break;
        if (k == K_ENTER) { ok = 1; break; }
        if (k == K_UP) f = f ? f - 1 : 3;
        else if (k == K_DOWN || k == K_TAB) f = (f + 1) & 3;
        else if ((k & 0xFF) == ' ') on[f] ^= 1;
        else
        {
            i = toupper(k & 0xFF);
            if (i == 'R') on[0] ^= 1;
            else if (i == 'A') on[1] ^= 1;
            else if (i == 'H') on[2] ^= 1;
            else if (i == 'S') on[3] ^= 1;
        }
    }
    Forma_cursor(1);
    if (!ok) return;
    na = 0;
    for (i = 0; i < 4; i++) if (on[i]) na |= fl[i];
    for (i = 0; i < p->n; i++) if (p->nsel ? p->f[i].sel : (i == p->cur)) {
        e = &p->f[i];
        if (!strcmp(e->name, "..")) continue;
        unir_ruta(path, p->path, e->name);
        if (_dos_getfileattr(path, &old)) continue;
        old = (old & ~0x27u) | na;
        if (e->attr & _A_SUBDIR) old &= ~(unsigned)_A_SUBDIR;
        _dos_setfileattr(path, old);
    }
    refrescar(act);
}

static void info_Dir(PANEL *p, FENT *e) {
    static const unsigned fl[4] = { _A_RDONLY, _A_ARCH, _A_HIDDEN, _A_SYSTEM };
    static const char *nmz[4] = { "Read-only", "Archive", "Hidden", "System" };
    char (*q)[80];
    int nq = 1, qi = 0, i, f = 0, trunc = 0, stop = 0, on[5], ok = 0;
    unsigned long bytes = 0, nfile = 0;
    unsigned ndir = 0, at = 0, na, old, rc;
    struct find_t ft;
    char sp[100], fp[100], b[60];
    unsigned k;

    q = (char (*)[80])malloc(200 * 80);
    if (!q) { Aviso("Error", "Out of memory"); return; }
    unir_ruta(q[0], p->path, e->name);
    Forma_cursor(0);
    Caja(22, 9, 36, 5, A_DLG, "Calculating...");
    poner_Txt(24, 10, A_DLG, "Esc = stop", 32);
    while (qi < nq && !stop)
    {
        fmt(b, "%lu files, %u directories", nfile, ndir);
        poner_Txt(24, 11, A_DLG, b, 32);
        volcar_rapido();
        unir_ruta(sp, q[qi], "*.*");
        rc = _dos_findfirst(sp, ATTR_ALL, &ft);
        while (!rc) {
            if (ft.name[0] == '.' && (!ft.name[1] || (ft.name[1] == '.' && !ft.name[2]))) { }
            else if (ft.attrib & _A_SUBDIR) {
                ndir++;
                if (nq < 200 && strlen(q[qi]) + 14 < 80) unir_ruta(q[nq++], q[qi], ft.name);
                else trunc = 1;
            } else { nfile++; bytes += ft.size; }
            if (hay_Esc()) { stop = 1; break; }
            rc = _dos_findnext(&ft);
        }
        qi++;
    }
    if (_dos_getfileattr(q[0], &at)) at = 0;
    for (i = 0; i < 4; i++) on[i] = (at & fl[i]) != 0;
    on[4] = 0;
    for (;;) {
        Caja(18, 4, 44, 17, A_DLG, "Directory");
        fmt(b, "%.12s", e->name);
        poner_Txt(20, 5, A_DLG, b, 40);
        fmt(b, "Total size  : %lu bytes", bytes);
        poner_Txt(20, 7, A_DLG, b, 40);
        fmt(b, "Files       : %lu", nfile);
        poner_Txt(20, 8, A_DLG, b, 40);
        fmt(b, "Directories : %u", ndir);
        poner_Txt(20, 9, A_DLG, b, 40);
        poner_Txt(20, 10, A_DLG, stop || trunc ? "(count is incomplete)" : "", 40);
        for (i = 0; i < 4; i++) {
            fmt(b, "[%c] %s", on[i] ? 'x' : ' ', nmz[i]);
            poner_Txt(22, 12 + i, i == f ? A_SELD : A_DLG, b, 20);
        }
        fmt(b, "[%c] Apply to contents too", on[4] ? 'x' : ' ');
        poner_Txt(22, 16, 4 == f ? A_SELD : A_DLG, b, 36);
        button(24, 18, "  Ok  ", 0);
        button(40, 18, " Cancel ", 0);
        poner_Txt(20, 20, A_DLG, "Space = mark   Enter = apply   Esc = exit", 40);
        k = Leer_Tecla();
        if (k == K_ESC) break;
        if (k == K_ENTER) { ok = 1; break; }
        if (k == K_UP) f = f ? f - 1 : 4;
        else if (k == K_DOWN || k == K_TAB) f = (f + 1) % 5;
        else if ((k & 0xFF) == ' ') on[f] ^= 1;
        else
        {
            i = toupper(k & 0xFF);
            if (i == 'R') on[0] ^= 1;
            else if (i == 'A') on[1] ^= 1;
            else if (i == 'H') on[2] ^= 1;
            else if (i == 'S') on[3] ^= 1;
        }
    }
    Forma_cursor(1);
    if (ok)
    {
        na = 0;
        for (i = 0; i < 4; i++) if (on[i]) na |= fl[i];
        for (i = 0; i < (on[4] ? nq : 1); i++) {
            if (_dos_getfileattr(q[i], &old) == 0)
                _dos_setfileattr(q[i], (old & ~0x27u & ~(unsigned)_A_SUBDIR) | na);
            if (i == 0 && !on[4]) break;
            unir_ruta(sp, q[i], "*.*");
            rc = _dos_findfirst(sp, ATTR_ALL, &ft);
            while (!rc)
            {
                if (!(ft.attrib & _A_SUBDIR)) {
                    unir_ruta(fp, q[i], ft.name);
                    _dos_setfileattr(fp, (ft.attrib & ~0x27u) | na);
                }
                rc = _dos_findnext(&ft);
            }
        }
        refrescar(act);
    }
    free(q);
}

static void Guardar_Estado(void)
{
    int i;
    memset(&st, 0, sizeof st);
    for (i = 0; i < 2; i++) {
        strcpy(st.path[i], pan[i].path);
        if (pan[i].n) strcpy(st.cur[i], pan[i].f[pan[i].cur].name);
        st.top[i] = pan[i].top;
        st.brief[i] = pan[i].brief;
        st.sort[i] = pan[i].sort;
    }
    st.act = act;
    _fmemcpy(&lsh->u.s, &st, sizeof st);
    lsh->have = 1;
}

static unsigned Valor_Hex(const char *s) {
    unsigned v = 0;
    int i, c;
    for (i = 0; i < 4; i++) {
        c = toupper(s[i]);
        if (c >= '0' && c <= '9') c -= '0';
        else if (c >= 'A' && c <= 'F') c -= 'A' - 10;
        else return 0;
        v = v * 16 + c;
    }
    return v;
}

static void Buscar_Cargador(int argc, char **argv)
{
    int i;
    LSHARE __far *l;
    for (i = 1; i < argc; i++) {
        if (strnicmp(argv[i], "/L:", 3) || strlen(argv[i]) != 12) continue;
        l = (LSHARE __far *)MK_FP(Valor_Hex(argv[i] + 3), Valor_Hex(argv[i] + 8));
        if (!_fmemcmp(l->sig, "NCL1", 4)) lsh = l;
    }
}

static int quiet;

static void Ejecutar(const char *c, int direct)
{
    PANEL *p = &pan[act];
    char b[260];
    const char *cs;
    int l;

    if (lsh)
    {
        unir_ruta(b, p->path, c);
        if (direct && strlen(b) < 80) {
            _fstrcpy(lsh->prog, b);
            b[0] = 0;
        } else {
            cs = getenv("COMSPEC");
            if (!cs || strlen(cs) >= 80) cs = "C:\\COMMAND.COM";
            _fstrcpy(lsh->prog, cs);
            fmt(b, " /C %.120s", c);
        }
        l = strlen(b);
        lsh->tail[0] = (unsigned char)l;
        _fmemcpy(lsh->tail + 1, b, l);
        lsh->tail[l + 1] = 13;
        Guardar_Estado();
        lsh->err = 0;
    }
    Poner_dir(p->path);
    if (!quiet) {
        Ver_Pant_dos();
        Forma_cursor(1);
        if (ucx) Poner_dos("\r\n");
        Poner_dos(p->path);
        Poner_dos(">");
        Poner_dos(c);
        Poner_dos("\r\n");
    }
    if (lsh) { lsh->run = 1; exit(1); }

    _nheapshrink();
    Fin_buffer();
    system(c);
    Ini_Video();
    Guardar_pant();
    Ini_Buffer();
    Forma_cursor(1);
    refrescar(0);
    refrescar(1);
}

static char extdir[80];
static char extbuf[1024];

static int Buscar_Ext(const char *name, char *out) {
    char path[100], *p, *q, *eol;
    const char *e = strrchr(name, '.'), *s;
    int fd, n, l, o;

    if (!e || !e[1]) return 0;
    e++;
    l = strlen(e);
    fmt(path, "%sNC.EXT", extdir);
    fd = open(path, O_RDONLY | O_BINARY);
    if (fd < 0) fd = open("NC.EXT", O_RDONLY | O_BINARY);
    if (fd < 0) return 0;
    n = read(fd, extbuf, sizeof(extbuf) - 1);
    close(fd);
    if (n <= 0) return 0;
    extbuf[n] = 0;
    for (p = extbuf; *p; p = eol) {
        eol = p;
        while (*eol && *eol != '\n') eol++;
        if (*eol) *eol++ = 0;
        while (*p == ' ' || *p == '\t') p++;
        if (*p == '#' || *p == ';' || !*p) continue;
        q = strchr(p, '=');
        if (!q || q - p != l || strnicmp(p, e, l)) continue;
        q++;
        while (*q == ' ') q++;
        o = 0;
        while (*q && *q != '\r' && o < 110) {
            if (*q == '%' && (q[1] == 'f' || q[1] == 'd' || q[1] == 'x')) {
                s = q[1] == 'f' ? name : q[1] == 'd' ? extdir :
#ifdef _X286
                    "286";
#else
                    "86";
#endif
                while (*s && o < 110) out[o++] = *s++;
                q += 2;
            } else out[o++] = *q++;
        }
        while (o && out[o - 1] == ' ') o--;
        out[o] = 0;
        return o > 0;
    }
    return 0;
}

static void Guardar_ini(void) {
    char path[100], b[80];
    int fd, l;
    fmt(path, "%sNC.INI", extdir);
    fd = open(path, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, S_IREAD | S_IWRITE);
    if (fd < 0) return;
    l = fmt(b, "B0=%d\r\nB1=%d\r\nS0=%d\r\nS1=%d\r\n", pan[0].brief, pan[1].brief, pan[0].sort, pan[1].sort);
    write(fd, b, l);
    close(fd);
}

static void leer_Ini(void)
{
    char path[100], *p;
    int fd, n, v;
    fmt(path, "%sNC.INI", extdir);
    fd = open(path, O_RDONLY | O_BINARY);
    if (fd < 0) return;
    n = read(fd, extbuf, sizeof(extbuf) - 1);
    close(fd);
    if (n <= 0) return;
    extbuf[n] = 0;
    for (p = extbuf; *p; p++) {
        if ((p == extbuf || p[-1] == '\n') && (p[0] == 'B' || p[0] == 'S') && (p[1] == '0' || p[1] == '1') && p[2] == '=') {
            v = atoi(p + 3);
            if (p[0] == 'B') pan[p[1] - '0'].brief = v != 0;
            else pan[p[1] - '0'].sort = v & 3;
        }
    }
}

static void Salir(void) {
    Poner_dir(pan[act].path);
    Ver_Pant_dos();
    Forma_cursor(1);
    exit(0);
}

static void Ejecutar_Linea(char *c) {
    char *a;
    while (*c == ' ') c++;
    if (!*c) return;
    if (c[1] == ':' && c[2] == 0) ir_A_Dir(act, c);
    else if (toupper(c[0]) == 'C' && toupper(c[1]) == 'D' &&
             (c[2] == ' ' || c[2] == '\\' || c[2] == '.' || c[2] == 0)) {
        a = c + 2;
        while (*a == ' ') a++;
        if (*a) ir_A_Dir(act, a);
    } else Ejecutar(c, 0);
    cmd[0] = 0; cmdlen = 0;
}

static int Pedir_buf(void)
{
    iobsz = 16384;
    while (iobsz >= 1024) {
        iob = (char *)malloc(iobsz);
        if (iob) return 0;
        iobsz >>= 1;
    }
    Aviso("Error", "Out of memory");
    return -1;
}

static void soltar_Buf(void) {
    free(iob);
    iob = NULL;
}

static int Sobrescribir(void)
{
    char t[100];
    int k;
    if (ovall || !existe(dp)) return 1;
    fmt(t, "%.45s already exists", dp);
    k = pedir_tecla("Warning", t, "Y = yes   N = no   A = all   Esc = cancel", "YNA");
    if (k == 27) { abortf = 1; return -1; }
    if (k == 'N') return 0;
    if (k == 'A') ovall = 1;
    return 1;
}

static int Copiar_Fich(void)
{
    char t[100];
    int fi, fo, n, k;
    unsigned dt, tm;

    if (!stricmp(sp, dp)) { Aviso("Error", "Source and destination are the same file"); return -1; }
    k = Sobrescribir();
    if (k < 0) return -1;
    if (k == 0) return 0;
    status("Copying", sp);
    fi = open(sp, O_RDONLY | O_BINARY);
    if (fi < 0) { fmt(t, "Cannot open %.40s", sp); Aviso("Error", t); return -1; }
    _dos_setfileattr(dp, _A_NORMAL);
    fo = open(dp, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, S_IREAD | S_IWRITE);
    if (fo < 0) { close(fi); fmt(t, "Cannot create %.40s", dp); Aviso("Error", t); return -1; }
    for (;;) {
        n = read(fi, iob, iobsz);
        if (n <= 0) break;
        if (write(fo, iob, n) != n) {
            close(fi); close(fo); remove(dp);
            Aviso("Error", "Write error (disk full?)");
            return -1;
        }
        if (hay_Esc()) {
            close(fi); close(fo); remove(dp);
            abortf = 1;
            return -1;
        }
    }
    _dos_getftime(fi, &dt, &tm);
    _dos_setftime(fo, dt, tm);
    close(fi);
    close(fo);
    return 0;
}

static int Copiar_Item(unsigned attr)
{
    struct find_t ft;
    unsigned rc;
    int ls, ld, r = 0;

    if (!(attr & _A_SUBDIR)) return Copiar_Fich();

    ls = strlen(sp);
    ld = strlen(dp);
    if (!strnicmp(dp, sp, ls) && (dp[ls] == '\\' || dp[ls] == 0)) {
        Aviso("Error", "Cannot copy a directory into itself");
        return -1;
    }
    if (ls + 14 >= PMAX || ld + 14 >= PMAX) { Aviso("Error", "Path too long"); return -1; }
    mkdir(dp);
    if (!Es_dir(dp)) { Aviso("Error", "Cannot create directory"); return -1; }
    strcpy(sp + ls, "\\*.*");
    dp[ld] = '\\';
    rc = _dos_findfirst(sp, ATTR_ALL, &ft);
    while (!rc && !abortf) {
        if (ft.name[0] != '.') {
            strcpy(sp + ls + 1, ft.name);
            strcpy(dp + ld + 1, ft.name);
            r = Copiar_Item(ft.attrib);
            if (r) break;
        }
        rc = _dos_findnext(&ft);
    }
    sp[ls] = 0;
    dp[ld] = 0;
    if (r) return r;
    return abortf ? -1 : 0;
}

static int borrar_Item(unsigned attr) {
    struct find_t ft;
    unsigned rc;
    int ls, r = 0;

    if (hay_Esc()) abortf = 1;
    if (abortf) return -1;
    if (attr & _A_SUBDIR) {
        ls = strlen(sp);
        if (ls + 14 >= PMAX) { Aviso("Error", "Path too long"); return -1; }
        strcpy(sp + ls, "\\*.*");
        rc = _dos_findfirst(sp, ATTR_ALL, &ft);
        while (!rc)
        {
            if (ft.name[0] != '.') {
                strcpy(sp + ls + 1, ft.name);
                r = borrar_Item(ft.attrib);
                if (r) break;
            }
            rc = _dos_findnext(&ft);
        }
        sp[ls] = 0;
        if (r) return r;
        if (rmdir(sp)) { Aviso("Error", "Cannot delete directory"); return -1; }
        return 0;
    }
    status("Deleting", sp);
    if (attr & (_A_RDONLY | _A_HIDDEN | _A_SYSTEM)) _dos_setfileattr(sp, _A_NORMAL);
    if (remove(sp)) { Aviso("Error", "Cannot delete file"); return -1; }
    return 0;
}

static int Mover_item(unsigned attr)
{
    int k;
    if (!stricmp(sp, dp)) return 0;
    if (toupper(sp[0]) == toupper(dp[0])) {
        if (!(attr & _A_SUBDIR) && existe(dp) && !Es_dir(dp)) {
            k = Sobrescribir();
            if (k < 0) return -1;
            if (k == 0) return 0;
            _dos_setfileattr(dp, _A_NORMAL);
            remove(dp);
        }
        if (!rename(sp, dp)) return 0;
    }
    if (Copiar_Item(attr)) return -1;
    return borrar_Item(attr);
}

static int contar_Sel(PANEL *p) {
    if (p->nsel) return p->nsel;
    if (p->n && strcmp(p->f[p->cur].name, "..")) return 1;
    return 0;
}

static int hay_Sel(PANEL *p, int i)
{
    return p->nsel ? p->f[i].sel : i == p->cur;
}

static unsigned long elegir_parte(void)
{
    static const char *nm[5] = { "Floppy 360K", "Floppy 720K", "Floppy 1.2M", "Floppy 1.44M", "Other size (KB)" };
    static const unsigned long sz[4] = { 362496UL, 730112UL, 1213952UL, 1457664UL };
    int f = 3, i;
    unsigned k;
    char b[80];
    Forma_cursor(0);
    for (;;) {
        Caja(23, 7, 34, 11, A_DLG, "Part size");
        for (i = 0; i < 5; i++) {
            fmt(b, " %-30s", nm[i]);
            poner_Txt(24, 9 + i, i == f ? A_SELD : A_DLG, b, 32);
        }
        k = Leer_Tecla();
        if (k == K_ESC) return 0;
        if (k == K_UP) f = f ? f - 1 : 4;
        else if (k == K_DOWN) f = (f + 1) % 5;
        else if (k == K_ENTER) break;
    }
    if (f < 4) return sz[f];
    strcpy(b, "1440");
    if (!pedir_Texto("Part size", "Size in KB:", b, 8)) return 0;
    return (unsigned long)atol(b) * 1024UL;
}

static int es_disquete(const char *p)
{
    return (toupper(p[0]) == 'A' || toupper(p[0]) == 'B') && p[1] == ':';
}

static void Nombre_Sin_Ext(const char *name, char *stem) {
    int j = 0;
    while (name[j] && name[j] != '.' && j < 8) { stem[j] = name[j]; j++; }
    stem[j] = 0;
}

static void hacer_dividir(void) {
    PANEL *p = &pan[act], *q = &pan[1 - act];
    FENT *e;
    unsigned long psz, left, tot;
    char src[100], dst[100], pn[100], stem[13], tmp[40];
    int fi, fo, part, np, n, ok;

    if (!p->n) return;
    e = &p->f[p->cur];
    if (e->attr & _A_SUBDIR) return;
    psz = elegir_parte();
    if (!psz) return;
    strcpy(dst, q->path);
    if (!pedir_Texto("Split", "Destination directory:", dst, 70)) return;
    np = (int)((e->size + psz - 1) / psz);
    if (np < 1) np = 1;
    if (np > 999) { Aviso("Error", "Too many parts (max 999)"); return; }
    Nombre_Sin_Ext(e->name, stem);
    unir_ruta(src, p->path, e->name);
    fi = open(src, O_RDONLY | O_BINARY);
    if (fi < 0) { Aviso("Error", "Cannot open file"); return; }
    if (Pedir_buf()) { close(fi); return; }
    abortf = 0;
    for (part = 1; part <= np && !abortf; part++) {
        if (es_disquete(dst) && part > 1) {
            fmt(tmp, "Insert disk for part %d", part);
            if (pedir_tecla("Split", tmp, "", "Y") != 'Y') break;
        }
        fmt(tmp, "%s.%03d", stem, part);
        unir_ruta(pn, dst, tmp);
        fo = open(pn, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, S_IREAD | S_IWRITE);
        if (fo < 0) { Aviso("Error", "Cannot create part"); break; }
        left = psz; ok = 1; tot = 0;
        while (left)
        {
            n = left > iobsz ? iobsz : (int)left;
            n = read(fi, iob, n);
            if (n <= 0) break;
            if (write(fo, iob, n) != n) { Aviso("Error", "Disk full"); ok = 0; break; }
            left -= n; tot += n;
            fmt(tmp, "Part %d of %d: %lu KB", part, np, tot >> 10);
            status("Split", tmp);
            if (hay_Esc()) { abortf = 1; ok = 0; break; }
        }
        close(fo);
        if (!ok) break;
    }
    close(fi);
    soltar_Buf();
    refrescar(0); refrescar(1);
}

static void hacer_Unir(void)
{
    PANEL *p = &pan[act], *q = &pan[1 - act];
    FENT *e;
    char dst[100], src[100], stem[13], tmp[40], *x;
    int first, part, fi, fo, n, ok = 1, any = 0;
    unsigned long tot = 0;

    if (!p->n) return;
    e = &p->f[p->cur];
    x = strrchr(e->name, '.');
    if ((e->attr & _A_SUBDIR) || !x || !isdigit((unsigned char)x[1])) {
        Aviso("Join", "Select the first part (for example FILE.001)");
        return;
    }
    first = atoi(x + 1);
    Nombre_Sin_Ext(e->name, stem);
    fmt(tmp, "%s.dat", stem);
    unir_ruta(dst, q->path, tmp);
    if (!pedir_Texto("Join", "Output file:", dst, 70)) return;
    if (Pedir_buf()) return;
    fo = open(dst, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, S_IREAD | S_IWRITE);
    if (fo < 0) { Aviso("Error", "Cannot create file"); soltar_Buf(); return; }
    abortf = 0;
    for (part = first; ok && !abortf; part++) {
        fmt(tmp, "%s.%03d", stem, part);
        unir_ruta(src, p->path, tmp);
        for (;;) {
            fi = open(src, O_RDONLY | O_BINARY);
            if (fi >= 0 || !es_disquete(p->path)) break;
            fmt(tmp, "Insert disk with part %d", part);
            if (pedir_tecla("Join", tmp, "", "Y") != 'Y') break;
        }
        if (fi < 0) break;
        any = 1;
        while ((n = read(fi, iob, iobsz)) > 0) {
            if (write(fo, iob, n) != n) { Aviso("Error", "Disk full"); ok = 0; break; }
            tot += n;
            fmt(tmp, "Part %d: %lu KB", part, tot >> 10);
            status("Join", tmp);
            if (hay_Esc()) { abortf = 1; break; }
        }
        close(fi);
    }
    close(fo);
    if (!any) Aviso("Error", "First part not found");
    soltar_Buf();
    refrescar(0); refrescar(1);
}

static void Hacer_formato(void) {
    static const char *cn[4] = { "360K", "720K", "1.2M", "1.44M" };
    static const char *cf[4] = { "360", "720", "1200", "1440" };
    int d = 0, c = 3, i;
    unsigned k;
    char b[80];

    Forma_cursor(0);
    for (;;) {
        Caja(25, 7, 30, 12, A_DLG, "Format disk");
        fmt(b, " Drive: %c:   (A / B)", 'A' + d);
        poner_Txt(26, 9, A_DLG, b, 28);
        for (i = 0; i < 4; i++) {
            fmt(b, " %-24s", cn[i]);
            poner_Txt(26, 11 + i, i == c ? A_SELD : A_DLG, b, 28);
        }
        k = Leer_Tecla();
        if (k == K_ESC) { Forma_cursor(1); return; }
        if (k == K_UP) c = c ? c - 1 : 3;
        else if (k == K_DOWN) c = (c + 1) & 3;
        else if (k == K_ENTER) break;
        else if (toupper(k & 0xFF) == 'A') d = 0;
        else if (toupper(k & 0xFF) == 'B') d = 1;
        else if (k == K_LEFT || k == K_RIGHT) d ^= 1;
    }
    Forma_cursor(1);
    fmt(b, "Everything on %c: will be erased. Continue?", 'A' + d);
    if (pedir_tecla("Format", b, "", "YN") != 'Y') return;
    fmt(b, "FORMAT %c: /F:%s", 'A' + d, cf[c]);
    Ejecutar(b, 0);
}

static void hacer_copiar(int mv) {
    PANEL *p = &pan[act];
    char in[80], dst[90], t[60];
    int i, cnt, dd, r;
    FENT *e;

    cnt = contar_Sel(p);
    if (!cnt) return;
    strcpy(in, pan[act ^ 1].path);
    fmt(t, "%s %d item(s) to:", mv ? "Move" : "Copy", cnt);
    ibfresh = 1;
    if (!pedir_Texto(mv ? "Move" : "Copy", t, in, 78) || !in[0]) return;
    ruta_Abs(dst, p->path, in);
    dd = Es_dir(dst);
    if (!dd && cnt > 1) { Aviso("Error", "Destination must be a directory"); return; }
    if (Pedir_buf()) return;
    ovall = 0; abortf = 0;
    for (i = 0; i < p->n && !abortf; i++) {
        if (!hay_Sel(p, i)) continue;
        e = &p->f[i];
        unir_ruta(sp, p->path, e->name);
        if (dd) unir_ruta(dp, dst, e->name); else strcpy(dp, dst);
        r = mv ? Mover_item(e->attr) : Copiar_Item(e->attr);
        if (r) break;
    }
    soltar_Buf();
    refrescar(0);
    refrescar(1);
}

static void hacer_borrar(void)
{
    PANEL *p = &pan[act];
    char t[60];
    int i, cnt;

    cnt = contar_Sel(p);
    if (!cnt) return;
    if (cnt == 1 && !p->nsel) fmt(t, "Delete %s ?", p->f[p->cur].name);
    else fmt(t, "Delete %d items ?", cnt);
    if (!confirmar("Delete", t)) return;
    abortf = 0;
    for (i = 0; i < p->n && !abortf; i++) {
        if (!hay_Sel(p, i)) continue;
        unir_ruta(sp, p->path, p->f[i].name);
        if (borrar_Item(p->f[i].attr)) break;
    }
    refrescar(0);
    refrescar(1);
}

static void hacer_Renombrar(void)
{
    PANEL *p = &pan[act];
    FENT *e = p->n ? &p->f[p->cur] : NULL;
    char in[80], s1[90], d[90], nm[13];
    if (!e || !strcmp(e->name, "..")) return;
    strcpy(in, e->name);
    ibhome = 1;
    if (!pedir_Texto("Rename", "New name:", in, 78) || !in[0] || !strcmp(in, e->name)) return;
    unir_ruta(s1, p->path, e->name);
    ruta_Abs(d, p->path, in);
    if (existe(d)) { Aviso("Error", "That name already exists"); return; }
    if (rename(s1, d)) { Aviso("Error", "Cannot rename"); return; }
    refrescar(0);
    refrescar(1);
    Quitar_Dir(d, nm);
    Buscar_Cursor(p, nm);
}

static void hacer_Fichero(void)
{
    PANEL *p = &pan[act];
    char in[80], d[90], nm[13];
    int fd;
    in[0] = 0;
    if (!pedir_Texto("Create file", "Name:", in, 78) || !in[0]) return;
    ruta_Abs(d, p->path, in);
    if (existe(d)) { Aviso("Error", "A file with that name already exists"); return; }
    fd = open(d, O_WRONLY | O_CREAT | O_EXCL | O_BINARY, S_IREAD | S_IWRITE);
    if (fd < 0) { Aviso("Error", "Cannot create file"); return; }
    close(fd);
    refrescar(0);
    refrescar(1);
    Quitar_Dir(d, nm);
    Buscar_Cursor(p, nm);
}

static void Hacer_Dir(void)
{
    PANEL *p = &pan[act];
    char in[80], d[90], nm[13];
    in[0] = 0;
    if (!pedir_Texto("Create directory", "Name:", in, 78) || !in[0]) return;
    ruta_Abs(d, p->path, in);
    if (mkdir(d)) { Aviso("Error", "Cannot create directory"); return; }
    refrescar(0);
    refrescar(1);
    Quitar_Dir(d, nm);
    Buscar_Cursor(p, nm);
}

static int Listar_Unidades(char *dr) {
    union REGS r;
    unsigned orig, n, cur, d;
    int k = 0, nfl;
    int86(0x11, &r, &r);
    nfl = (r.x.ax & 1) ? ((r.x.ax >> 6) & 3) + 1 : 0;
    _dos_getdrive(&orig);
    for (d = 1; d <= 26; d++) {
        if (d <= 2) { if ((int)d <= nfl) dr[k++] = (char)('A' + d - 1); continue; }
        _dos_setdrive(d, &n);
        _dos_getdrive(&cur);
        if (cur == d) dr[k++] = (char)('A' + d - 1);
    }
    _dos_setdrive(orig, &n);
    dr[k] = 0;
    return k;
}

static void hacer_unidad(int i)
{
    char dr[28], a[3], t[4];
    int n, sel = 0, w, x, x0, j, c;
    unsigned k;

    n = Listar_Unidades(dr);
    if (!n) return;
    for (j = 0; j < n; j++) if (dr[j] == toupper(pan[i].path[0])) sel = j;
    w = n * 3 + 4;
    if (w < 20) w = 20;
    if (w > 80) w = 80;
    x = pan[i].x + (40 - w) / 2;
    if (x < 0) x = 0;
    if (x + w > 80) x = 80 - w;
    x0 = x + (w - n * 3) / 2;
    Forma_cursor(0);
    for (;;)
    {
        Caja(x, 9, w, 3, A_DLG, "Drive");
        for (j = 0; j < n; j++) {
            fmt(t, " %c ", dr[j]);
            poner_Txt(x0 + j * 3, 10, j == sel ? A_SELD : A_DLG, t, 3);
        }
        k = Leer_Tecla();
        if (k == K_ESC) { Forma_cursor(1); return; }
        if (k == K_ENTER) break;
        if (k == K_LEFT) sel = sel ? sel - 1 : n - 1;
        else if (k == K_RIGHT) sel = sel < n - 1 ? sel + 1 : 0;
        else
        {
            c = toupper(k & 0xFF);
            for (j = 0; j < n; j++) if (dr[j] == c) break;
            if (j < n) { sel = j; break; }
        }
    }
    Forma_cursor(1);
    j = dr[sel];

    if (toupper(pan[1 - i].path[0]) == j) {
        cambiar_panel(&pan[i], pan[1 - i].path, NULL);
        return;
    }
    a[0] = dr[sel]; a[1] = ':'; a[2] = 0;
    ir_A_Dir(i, a);
}

typedef long cnum_t;
#define CL(v) ((v) / 10)
#define CI(n) ((cnum_t)(n) * 10)

static const char *cp;
static int cerr;

static cnum_t C_expr(void);

static void c_saltar(void) {
    while (*cp == ' ') cp++;
}

static int C_Digito(int c, int base)
{
    int v;
    c = toupper(c);
    if (c >= '0' && c <= '9') v = c - '0';
    else if (c >= 'A' && c <= 'F') v = c - 'A' + 10;
    else return -1;
    return v < base ? v : -1;
}

static cnum_t C_Numero(void) {
    const char *s = cp, *e;
    unsigned long v = 0;
    int base = 10, d;

    if (*s == '$') { base = 16; s++; }
    else if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) { base = 16; s += 2; }
    else
    {
        e = s;
        while (C_Digito(*e, 16) >= 0) e++;
        if (*e == 'h' || *e == 'H') base = 16;
        else if (s[0] == '0' && (s[1] == 'b' || s[1] == 'B') && C_Digito(s[2], 2) >= 0) { base = 2; s += 2; }
    }
    if (base == 10) {
        int any = 0, dec = 0;
        while (*s >= '0' && *s <= '9') { v = v * 10 + (*s - '0'); s++; any = 1; }
        if (*s == '.') {
            s++;
            if (*s >= '0' && *s <= '9') dec = *s - '0';
            while (*s >= '0' && *s <= '9') { s++; any = 1; }
        }
        if (!any) { cerr = 1; return 0; }
        cp = s;
        return (cnum_t)(v * 10 + dec);
    }
    if (C_Digito(*s, base) < 0) { cerr = 1; return 0; }
    while ((d = C_Digito(*s, base)) >= 0) { v = v * base + d; s++; }
    if (base == 16 && (*s == 'h' || *s == 'H')) s++;
    cp = s;
    return CI((long)v);
}

static cnum_t c_valor_Simple(void)
{
    cnum_t v;
    c_saltar();
    if (*cp == '(') {
        cp++;
        v = C_expr();
        c_saltar();
        if (*cp == ')') cp++; else cerr = 1;
        return v;
    }
    if (*cp == '-') { cp++; return -c_valor_Simple(); }
    if (*cp == '+') { cp++; return c_valor_Simple(); }
    if (*cp == '~') { cp++; return CI(~CL(c_valor_Simple())); }
    return C_Numero();
}

static cnum_t c_mult(void)
{
    cnum_t v = c_valor_Simple(), r, q;
    int op;
    for (;;)
    {
        c_saltar();
        op = *cp;
        if (op != '*' && op != '/' && op != '%') return v;
        cp++;
        r = c_valor_Simple();
        if (op == '*') v = (v / 10) * r + ((v % 10) * r) / 10;
        else if (r == 0) { cerr = 2; return 0; }
        else if (op == '/') { q = v / r; v = q * 10 + ((v % r) * 10) / r; }
        else v %= r;
    }
}

static cnum_t C_suma(void)
{
    cnum_t v = c_mult();
    int op;
    for (;;)
    {
        c_saltar();
        op = *cp;
        if (op != '+' && op != '-') return v;
        cp++;
        if (op == '+') v += c_mult(); else v -= c_mult();
    }
}

static cnum_t C_desplazar(void) {
    cnum_t v = C_suma();
    unsigned long u;
    int op, n;
    for (;;) {
        c_saltar();
        if ((cp[0] != '<' && cp[0] != '>') || cp[1] != cp[0]) return v;
        op = *cp;
        cp += 2;
        n = (int)(CL(C_suma()) & 31);
        u = (unsigned long)CL(v);
        v = CI((long)(op == '<' ? (u << n) : (u >> n)));
    }
}

static cnum_t C_Bit_Y(void)
{
    cnum_t v = C_desplazar();
    for (;;) { c_saltar(); if (*cp != '&') return v; cp++; v = CI(CL(v) & CL(C_desplazar())); }
}

static cnum_t c_xor(void) {
    cnum_t v = C_Bit_Y();
    for (;;) { c_saltar(); if (*cp != '^') return v; cp++; v = CI(CL(v) ^ CL(C_Bit_Y())); }
}

static cnum_t C_expr(void)
{
    cnum_t v = c_xor();
    for (;;) { c_saltar(); if (*cp != '|') return v; cp++; v = CI(CL(v) | CL(c_xor())); }
}

static int C_Evaluar(const char *s, cnum_t *out)
{
    cp = s;
    cerr = 0;
    c_saltar();
    if (!*cp) return 1;
    *out = C_expr();
    c_saltar();
    if (!cerr && *cp) cerr = 1;
    return cerr;
}

static void fmt_Dec(char *o, cnum_t v)
{
    unsigned long a = v < 0 ? (unsigned long)(-v) : (unsigned long)v;
    if (v < 0) *o++ = '-';
    if (a % 10) fmt(o, "%lu.%lu", a / 10, a % 10);
    else fmt(o, "%lu", a / 10);
}

static void calculadora(void)
{
    static char ex[45];
    char t[60];
    int l, x = 14, y = 6, w = 52, i, j, r, isint;
    cnum_t v = 0;
    long lv = 0;
    unsigned k;
    unsigned long u;
    char t2[32];
    l = strlen(ex);
    for (;;) {
        Caja(x, y, w, 9, A_DLG, "Calculator");
        poner_Txt(x + 2, y + 1, A_DLG, ">", 1);
        poner_Txt(x + 4, y + 1, A_INP, ex, 45);
        r = C_Evaluar(ex, &v);
        if (!l)
        {
            poner_Txt(x + 2, y + 3, A_DLG, "E.g.: 10/4  1.5*3  0b1010<<2  (1Fh+$20)*3", w - 4);
        } else if (r) {
            poner_Txt(x + 2, y + 3, A_DLG,
                   r == 2 ? "Division by zero" : "...", w - 4);
        } else {
            fmt_Dec(t2, v);
            fmt(t, "Dec: %s", t2);
            poner_Txt(x + 2, y + 3, A_DLG, t, w - 4);
            isint = (v % 10) == 0;
            lv = v / 10;
            if (isint)
            {
                u = (unsigned long)lv;
                fmt(t, "Hex: %lX", u);
                poner_Txt(x + 2, y + 4, A_DLG, t, w - 4);
                strcpy(t, "Bin: ");
                j = 5;
                i = 31;
                while (i > 0 && !((u >> i) & 1)) i--;
                for (; i >= 0; i--) {
                    t[j++] = (char)('0' + (int)((u >> i) & 1));
                    if (i && !(i & 7)) t[j++] = ' ';
                }
                t[j] = 0;
                poner_Txt(x + 2, y + 5, A_DLG, t, w - 4);
            }
        }
        poner_Txt(x + 2, y + 7, A_DLG, "Enter = use result   Esc = close", w - 4);
        pos_cursor(x + 4 + l, y + 1);
        k = Leer_Tecla();
        if (k == K_ESC) break;
        if (k == K_ENTER) {
            if (l && !r)
            {
                fmt_Dec(ex, v);
                l = strlen(ex);
            }
            continue;
        }
        if (k == K_BS) { if (l) ex[--l] = 0; continue; }
        k &= 0xFF;
        if (k >= 32 && k < 127 && l < 44) { ex[l++] = (char)k; ex[l] = 0; }
    }
}

static void Calc_flotante(void) {
    int x = 14, y = 6, w = 52, h = 9, r, c;
    unsigned short *sv = popbuf;
    unsigned cx, dx;
    union REGS rg;

    if (incalc) return;
    incalc = 1;
    rg.h.ah = 3; rg.h.bh = 0;
    int86(0x10, &rg, &rg);
    cx = rg.x.cx; dx = rg.x.dx;
    for (r = 0; r <= h; r++)
        for (c = 0; c < w + 2; c++) sv[r * (w + 2) + c] = vid[(y + r) * 80 + x + c];
    calculadora();
    vdirty = 1;
    for (r = 0; r <= h; r++)
        for (c = 0; c < w + 2; c++) vid[(y + r) * 80 + x + c] = sv[r * (w + 2) + c];
    Volcar();
    rg.h.ah = 1; rg.x.cx = cx;
    int86(0x10, &rg, &rg);
    rg.h.ah = 2; rg.h.bh = 0; rg.x.dx = dx;
    int86(0x10, &rg, &rg);
    incalc = 0;
}

static void hacer_Buscar(void);

static void Hacer_comparar(void)
{
    int i, j, d, n0, n1;
    FENT *a, *b;
    for (d = 0; d < 2; d++) {
        PANEL *p = &pan[d], *o = &pan[1 - d];
        for (i = 0; i < p->n; i++) {
            a = &p->f[i];
            a->sel = 0;
            if (a->attr & _A_SUBDIR) continue;
            a->sel = 1;
            for (j = 0; j < o->n; j++) {
                b = &o->f[j];
                if (!(b->attr & _A_SUBDIR) && !strcmp(a->name, b->name)) {
                    if (a->size == b->size && a->date == b->date && a->tim == b->tim)
                        a->sel = 0;
                    break;
                }
            }
        }
        recontar(p);
    }
    n0 = pan[0].nsel; n1 = pan[1].nsel;
    if (!n0 && !n1) Aviso("Compare", "The directories are the same");
}

static int num_Items(int m) {
    if (m == 0 || m == NMENU - 1) return 5;
    if (m == 4) return 5;
    if (m == 3) return 1;
    if (m == 2) return 1;
    if (m == 1) return 10;
    return 0;
}

static void Texto_Item(int m, int it, char *t) {
    if (m == 1) {
        if (it == 0) fmt(t, " %-15s%7s", "Find files", "Ctrl+F");
        else if (it == 1) fmt(t, " %-15s%7s", "Make directory", "F7");
        else if (it == 2) fmt(t, " %-15s%7s", "Make file", "Alt+F7");
        else if (it == 3) fmt(t, " %-15s%7s", "Rename", "Alt+F6");
        else if (it == 4) fmt(t, " %-15s%7s", "Mass rename", "");
        else if (it == 5) fmt(t, " %-15s%7s", "Attributes", "Ctrl+A");
        else if (it == 6) fmt(t, " %-15s%7s", "Invert select", "*");
        else if (it == 7) fmt(t, " %-15s%7s", "Split file", "");
        else if (it == 8) fmt(t, " %-15s%7s", "Join files", "");
        else fmt(t, " %-15s%7s", "Format disk", "");
    } else if (m == 3) {
        strcpy(t, " About");
    } else if (m == 2) {
        fmt(t, " %-15s%7s", "Compare dirs", "Ctrl+D");
    } else if (m == 4) {
        if (it == 0) fmt(t, " %-15s%7s", "Calculator", "Ctrl+C");
        else if (it == 1) fmt(t, " %-15s%7s", "CD Player", "Ctrl+P");
        else if (it == 2) fmt(t, " %-15s%7s", "Agenda", "");
        else if (it == 3) fmt(t, " %-15s%7s", "ASCII table", "");
        else fmt(t, " %-15s%7s", "Compare files", "");
    }
    else if (it == 0) strcpy(t, " Select only dirs");
    else if (it == 1) strcpy(t, " Select only files");
    else if (it == 3) fmt(t, " %-15sCtrl+F%d", pan[m ? 1 : 0].brief ? "Full mode" : "Brief mode", m ? 2 : 1);
    else if (it == 4) {
        static const char *sn[4] = { "name", "ext", "date", "size" };
        fmt(t, " Sort: %-9s Ctrl+F3-F6", sn[pan[m ? 1 : 0].sort]);
    }
    else fmt(t, " Drive          Alt+F%d", m ? 2 : 1);
}

static void hacer_acerca(void)
{
    Caja(18, 8, 44, 9, A_DLG, "About");
    poner_Txt(20, 10, A_DLG, "          Noname Commander", 40);
    poner_Txt(20, 12, A_DLG, "        Programado por TheElf", 40);
    poner_Txt(20, 13, A_DLG, "     Thank for using my software!", 40);
    button(36, 14, "  Ok  ", 1);
    Forma_cursor(0);
    Leer_Tecla();
    Forma_cursor(1);
}

static void Ejecutar_util(const char *args)
{
    char c[130];
    int n;
    n = fmt(c, "%sutils.exe %s", extdir, args);
    if (n > 120) { Aviso("Error", "Path too long"); return; }
    quiet = extdir[0] != 0;
    Ejecutar(c, 0);
    quiet = 0;
}

static void comparar_fich(void)
{
    PANEL *p = &pan[act], *q = &pan[1 - act];
    FENT *e, *f = NULL;
    char fb[100], args[110];
    int i, n1 = -1, n2 = -1;

    if (p->nsel == 2) {
        for (i = 0; i < p->n; i++) if (p->f[i].sel) { if (n1 < 0) n1 = i; else n2 = i; }
        e = &p->f[n1]; f = &p->f[n2];
        strcpy(fb, f->name);
    } else {
        if (!p->n || !q->n) return;
        e = &p->f[p->cur]; f = &q->f[q->cur];
        unir_ruta(fb, q->path, f->name);
    }
    if ((e->attr & _A_SUBDIR) || (f->attr & _A_SUBDIR))
    {
        Aviso("Compare", "Select one file in each panel");
        return;
    }
    fmt(args, "-diff %s %s", e->name, fb);
    Ejecutar_util(args);
}

static char mrn[24] = "*", mre[12] = "*", mrf[24], mrr[24], mrs[8] = "1";

static void Aplicar_mascara(const char *mask, const char *orig, long num, char *o, int max)
{
    int n = 0, w, l;
    char t[12];
    while (*mask && n < max - 1) {
        if (*mask == '*') {
            for (l = 0; orig[l] && n < max - 1; l++) o[n++] = orig[l];
            mask++;
        } else if (*mask == '#') {
            w = 0;
            while (*mask == '#') { w++; mask++; }
            l = fmt(t, "%ld", num);
            for (; l < w && n < max - 1; l++) o[n++] = '0';
            for (w = 0; t[w] && n < max - 1; w++) o[n++] = t[w];
        } else o[n++] = *mask++;
    }
    o[n] = 0;
}

static void Reemplazar_Todo(char *s, const char *f, const char *r, int max)
{
    char t[80];
    int n = 0, lf = strlen(f);
    char *p = s;
    if (!lf) return;
    while (*p && n < max - 1)
    {
        if (!strnicmp(p, f, lf))
        {
            const char *q = r;
            while (*q && n < max - 1) t[n++] = *q++;
            p += lf;
        } else t[n++] = *p++;
    }
    t[n] = 0;
    strcpy(s, t);
}

static void nombre_masa(const char *old, long num, char *out) {
    char base[14], ext[6], nb[40], ne[16], full[80], *dot;
    int i;
    strcpy(full, old);
    dot = strrchr(full, '.');
    if (dot && dot != full) { *dot = 0; strncpy(ext, dot + 1, 4); ext[4] = 0; } else ext[0] = 0;
    strncpy(base, full, 12); base[12] = 0;
    Aplicar_mascara(mrn[0] ? mrn : "*", base, num, nb, 40);
    Aplicar_mascara(mre[0] ? mre : "*", ext, num, ne, 16);
    if (ne[0]) fmt(full, "%s.%s", nb, ne); else strcpy(full, nb);
    Reemplazar_Todo(full, mrf, mrr, 78);
    dot = strrchr(full, '.');
    if (dot && dot != full) { *dot = 0; strncpy(ne, dot + 1, 3); ne[3] = 0; } else ne[0] = 0;
    strncpy(nb, full, 8); nb[8] = 0;
    for (i = 0; nb[i]; i++) if (nb[i] == ' ') nb[i] = '_';
    if (ne[0]) fmt(out, "%s.%s", nb, ne); else strcpy(out, nb);
    strlwr(out);
}

static int formar_masa(PANEL *p, int *ix, int cnt) {
    static const char *lab[5] = { "Name:", "Extension:", "Find:", "Replace with:", "Start at:" };
    char *val[5];
    static const int mx[5] = { 20, 8, 20, 20, 5 };
    int f = 0, i, nn;
    unsigned k;
    long start;
    char b[90], nm[13];

    val[0] = mrn; val[1] = mre; val[2] = mrf; val[3] = mrr; val[4] = mrs;
    Forma_cursor(0);
    for (;;)
    {
        Caja(8, 1, 64, 22, A_DLG, "Mass rename");
        for (i = 0; i < 5; i++) {
            poner_Txt(10, 3 + i, A_DLG, lab[i], 13);
            fmt(b, " %-22s", val[i]);
            poner_Txt(24, 3 + i, i == f ? A_BTNF : A_INP, b, 24);
            if (i == f) poner_car(22, 3 + i, A_DLG, 0x10);
        }
        poner_Txt(10, 9, A_DLG, "*  = original name or extension      ## = counter (01, 02...)", 60);
        poner_Txt(10, 10, A_DLG, "Find/Replace with: changes one text for another in the name", 60);
        linea_H(9, 11, 62, A_DLG, 0xC4);
        poner_Txt(10, 11, A_DLG, " Result ", 11);
        start = atol(mrs);
        nn = cnt < 6 ? cnt : 6;
        for (i = 0; i < 6; i++) {
            if (i < nn)
            {
                nombre_masa(p->f[ix[i]].name, start + i, nm);
                fmt(b, " %-12s -> %-12s", p->f[ix[i]].name, nm);
                poner_Txt(10, 12 + i, A_DLG, b, 60);
            } else poner_Txt(10, 12 + i, A_DLG, i == nn && cnt > 6 ? "" : "", 60);
        }
        if (cnt > 6) {
            fmt(b, " ... and %d more (%d files in total)", cnt - 6, cnt);
            poner_Txt(10, 18, A_DLG, b, 60);
        }
        button(24, 19, "  Ok  ", f == 5);
        button(42, 19, " Cancel ", f == 6);
        poner_Txt(10, 21, A_DLG, "Arrows/Tab = move   Enter = edit   F10 = apply   Esc = exit", 60);
        k = Leer_Tecla();
        if (k == K_ESC) return 0;
        if (k == K_F10) return 1;
        if (k == K_UP) f = f ? f - 1 : 6;
        else if (k == K_DOWN || k == K_TAB) f = (f + 1) % 7;
        else if (k == K_LEFT && f >= 5) f = f == 5 ? 6 : 5;
        else if (k == K_RIGHT && f >= 5) f = f == 5 ? 6 : 5;
        else if (k == K_ENTER) {
            if (f == 5) return 1;
            if (f == 6) return 0;
            ibfresh = 1;
            pedir_Texto("Mass rename", lab[f], val[f], mx[f]);
            f++;
        }
    }
}

static void Hacer_masa(void)
{
    PANEL *p = &pan[act];
    int *ix, i, n = 0, cnt = 0, top = 0, rows = 13, fail = 0, ren = 0;
    char (*nw)[13], po[100], pn[100], pt[100];
    long start;
    unsigned k;
    char b[90];

    for (i = 0; i < p->n; i++)
        if (!(p->f[i].attr & _A_SUBDIR) && (!p->nsel || p->f[i].sel)) cnt++;
    if (!cnt) { Aviso("Rename", "No files to rename"); return; }
    ix = (int *)malloc(cnt * sizeof(int));
    nw = (char (*)[13])malloc(cnt * 13);
    if (!ix || !nw) { free(ix); free(nw); Aviso("Error", "Out of memory"); return; }
    for (i = 0; i < p->n; i++)
        if (!(p->f[i].attr & _A_SUBDIR) && (!p->nsel || p->f[i].sel)) ix[n++] = i;
    if (!formar_masa(p, ix, cnt)) { free(ix); free(nw); return; }
    start = atol(mrs);
    for (i = 0; i < cnt; i++) nombre_masa(p->f[ix[i]].name, start + i, nw[i]);

    Forma_cursor(0);
    for (;;)
    {
        Caja(8, 3, 64, 19, A_DLG, "Preview");
        for (i = 0; i < rows; i++) {
            if (top + i < cnt) {
                fmt(b, " %-12s -> %-12s %s", p->f[ix[top + i]].name, nw[top + i],
                    strcmp(p->f[ix[top + i]].name, nw[top + i]) ? "" : "(same)");
                poner_Txt(9, 5 + i, A_DLG, b, 62);
            } else poner_Txt(9, 5 + i, A_DLG, "", 62);
        }
        fmt(b, " %d files   Enter = rename   Esc = cancel", cnt);
        linea_H(9, 19, 62, A_DLG, 0xC4);
        poner_Txt(9, 20, A_DLG, b, 62);
        k = Leer_Tecla();
        if (k == K_ESC) { free(ix); free(nw); Forma_cursor(1); return; }
        if (k == K_ENTER) break;
        if (k == K_UP) { if (top) top--; }
        else if (k == K_DOWN) { if (top + rows < cnt) top++; }
        else if (k == K_PGUP) { top -= rows; if (top < 0) top = 0; }
        else if (k == K_PGDN) { if (top + rows < cnt) top += rows; if (top + rows > cnt && cnt > rows) top = cnt - rows; }
    }
    Forma_cursor(1);

    for (i = 0; i < cnt; i++) {
        nw[i][12] = 0;
        if (!strcmp(p->f[ix[i]].name, nw[i]) || !nw[i][0]) { nw[i][12] = 2; continue; }
        unir_ruta(po, p->path, p->f[ix[i]].name);
        fmt(b, "~rn%04d.tmp", i);
        unir_ruta(pt, p->path, b);
        if (rename(po, pt)) { nw[i][12] = 2; fail++; }
    }

    for (i = 0; i < cnt; i++) {
        if (nw[i][12] == 2) continue;
        fmt(b, "~rn%04d.tmp", i);
        unir_ruta(pt, p->path, b);
        unir_ruta(pn, p->path, nw[i]);
        if (existe(pn) || rename(pt, pn))
        {
            unir_ruta(po, p->path, p->f[ix[i]].name);
            rename(pt, po);
            fail++;
        } else ren++;
    }
    free(ix); free(nw);
    refrescar(act);
    if (fail)
    {
        fmt(b, "%d renamed, %d with errors (already exists)", ren, fail);
        Aviso("Mass rename", b);
    }
}

static void ejecutar_Item(int m, int it) {
    int side = m ? 1 : 0;
    if (m == 1) {
        if (it == 0) hacer_Buscar();
        else if (it == 1) Hacer_Dir();
        else if (it == 2) hacer_Fichero();
        else if (it == 3) hacer_Renombrar();
        else if (it == 4) Hacer_masa();
        else if (it == 5) Hacer_Atrib();
        else if (it == 6) invertir_Sel(&pan[act]);
        else if (it == 7) hacer_dividir();
        else if (it == 8) hacer_Unir();
        else Hacer_formato();
    } else if (m == 2) {
        Hacer_comparar();
    } else if (m == 3) {
        hacer_acerca();
    } else if (m == 4) {
        if (it == 0) calculadora();
        else if (it == 1) Repro_cd();
        else if (it == 2) Ejecutar_util("-agenda");
        else if (it == 3) Ejecutar_util("-ascii");
        else comparar_fich();
    }
    else if (it == 0) Sel_solo(&pan[side], 1);
    else if (it == 1) Sel_solo(&pan[side], 0);
    else if (it == 3) { pan[side].brief ^= 1; Ajustar_vista(&pan[side]); Guardar_ini(); }
    else if (it == 4) { pan[side].sort = (pan[side].sort + 1) & 3; Reordenar(&pan[side]); Guardar_ini(); }
    else hacer_unidad(side);
}

static void Hacer_Menu(void)
{
    int m = act ? NMENU - 1 : 0, it = 0, n, j, x, w = 26, full = 1;
    unsigned k;
    char t[40];

    Forma_cursor(0);
    for (;;) {
        n = num_Items(m);
        x = mpos[m] - 1;
        if (full)
        {

            dib_todo();
            Forma_cursor(0);
            j = fmt(t, " %s ", mtitle[m]);
            poner_Txt(x, 0, A_SELD, t, j);
            poner_car(x + 1, 0, A_SELHOT, mtitle[m][0]);
            if (n) Caja(x, 1, w, n + 2, A_DLG, NULL);
            full = 0;
        }

        for (j = 0; j < n; j++) {
            Texto_Item(m, j, t);
            poner_Hot(x + 1, 2 + j, j == it ? A_SELD : A_DLG, j == it ? A_SELHOT : A_HOT, t, w - 2);
        }
        k = Leer_Tecla();
        if (k == K_ESC || k == K_F9 || k == K_F10) break;
        if (k == K_LEFT) { m = (m + NMENU - 1) % NMENU; it = 0; full = 1; }
        else if (k == K_RIGHT) { m = (m + 1) % NMENU; it = 0; full = 1; }
        else if (n && k == K_UP) it = it ? it - 1 : n - 1;
        else if (n && k == K_DOWN) it = (it + 1) % n;
        else if (n && k == K_ENTER) { Forma_cursor(1); ejecutar_Item(m, it); return; }
    }
    Forma_cursor(1);
}

static int vfd;
static unsigned char *vlb;

static int Leer_en(long pos, unsigned char *b, int n)
{
    lseek(vfd, pos, SEEK_SET);
    n = read(vfd, b, n);
    return n < 0 ? 0 : n;
}

static int Byte_En(long pos)
{
    unsigned char c;
    return Leer_en(pos, &c, 1) == 1 ? c : -1;
}

static long Inicio_linea(long q) {
    long from;
    int n, i;
    if (q <= 0) return 0;
    from = q > 256 ? q - 256 : 0;
    n = Leer_en(from, vlb, (int)(q - from));
    for (i = n - 1; i >= 0; i--) if (vlb[i] == '\n') return from + i + 1;
    return from;
}

static long Linea_Previa(long pos)
{
    long e = pos, r;
    if (pos <= 0) return 0;
    if (Byte_En(pos - 1) == '\n') {
        e--;
        if (e > 0 && Byte_En(e - 1) == '\r') e--;
    }
    r = Inicio_linea(e);
    while (e - r > 80) r += 80;
    return r;
}

static char vsrch[40];
static long vmpos = -1;
static int vmlen;

static long ver_buscar(long from, long size, unsigned char *b)
{
    int n, i, j, l = strlen(vsrch);
    long pos = from;
    if (!l) return -1;
    while (pos < size)
    {
        lseek(vfd, pos, SEEK_SET);
        n = read(vfd, b, 4096);
        if (n < l) return -1;
        for (i = 0; i + l <= n; i++) {
            for (j = 0; j < l; j++)
                if (toupper(b[i + j]) != toupper((unsigned char)vsrch[j])) break;
            if (j == l) return pos + i;
        }
        pos += n - l + 1;
        if (_bios_keybrd(_KEYBRD_READY) && (_bios_keybrd(_KEYBRD_READ) & 0xFF) == 27) return -2;
    }
    return -1;
}

static void Visor_base(const char *fn) {
    long size, top = 0, lo[24], dtop = -1, fp;
    int at;
    int dhex = -1;
    int hex = 0, r, i, n, x, k, c;
    unsigned char *b;
    char t[100];
    unsigned key;

    b = (unsigned char *)malloc(4096 + 256);
    if (!b) { Aviso("Error", "Out of memory"); return; }
    vlb = b + 4096;
    vmpos = -1;
    vfd = open(fn, O_RDONLY | O_BINARY);
    if (vfd < 0) { free(b); Aviso("Error", "Cannot open file"); return; }
    size = lseek(vfd, 0L, SEEK_END);
    Forma_cursor(0);
    for (;;)
    {
        if (top == dtop && hex == dhex) goto waitkey;
        dtop = top; dhex = hex;
        fmt(t, " %.50s  %ld bytes  %s", fn, size, hex ? "[HEX]" : "[TEXT]");
        poner_Txt(0, 0, A_KEYL, t, 80);
        if (hex)
        {
            n = Leer_en(top, b, 16 * 23);
            for (r = 0; r < 23; r++) {
                i = r * 16;
                if (i >= n) { linea_H(0, r + 1, 80, A_TXT, ' '); continue; }
                x = fmt(t, "%08lX ", top + i);
                for (k = 0; k < 16; k++) {
                    if (i + k < n) x += fmt(t + x, "%02X ", b[i + k]);
                    else x += fmt(t + x, "   ");
                }
                poner_Txt(0, r + 1, A_TXT, t, 80);
                for (k = 0; k < 16 && i + k < n; k++) poner_car(58 + k, r + 1, A_TXT, b[i + k] ? b[i + k] : '.');
            }
        } else {
            n = Leer_en(top, b, 4096);
            i = 0;
            for (r = 0; r < 23; r++) {
                lo[r] = top + i;
                x = 0;
                while (i < n && x < 80)
                {
                    c = b[i++];
                    if (c == '\n') break;
                    if (c == '\r') continue;
                    if (c == '\t') { do poner_car(x++, r + 1, A_TXT, ' '); while (x < 80 && (x & 7)); continue; }
                    at = (vmpos >= 0 && top + i - 1 >= vmpos && top + i - 1 < vmpos + vmlen) ? A_SELD : A_TXT;
                    poner_car(x++, r + 1, at, c ? c : ' ');
                }
                if (x >= 80) {
                    if (i < n && b[i] == '\r') i++;
                    if (i < n && b[i] == '\n') i++;
                }
                linea_H(x, r + 1, 80 - x, A_TXT, ' ');
            }
            lo[23] = top + i;
        }
        Dib_Teclas(viewkeys);
waitkey:
        key = Leer_Tecla();
        if (key == K_DOWN || key == K_UP || key == K_PGDN || key == K_PGUP) vaciar_teclas();
        if (key == K_ESC || key == K_F3 || key == K_F10) break;
        if (key == K_F4) {
            hex ^= 1;
            if (hex) top &= ~15L; else top = Inicio_linea(top);
            continue;
        }
        if (key == K_F7 || key == K_SF7 || key == 'n' || key == 'N' ||
            ((key & 0xFF) == 'n' || (key & 0xFF) == 'N')) {
            if (key == K_F7 || !vsrch[0]) {
                char q[40];
                strcpy(q, vsrch);
                if (!pedir_Texto("Find", "Text to find:", q, 38) || !q[0]) { dtop = -1; continue; }
                strcpy(vsrch, q);
                fp = hex ? top : Inicio_linea(top);
            } else fp = vmpos >= 0 ? vmpos + 1 : top;
            fp = ver_buscar(fp, size, b);
            if (fp == -2) { dtop = -1; continue; }
            if (fp < 0)
            {
                vmpos = -1;
                Aviso("Find", "Not found");
                dtop = -1;
                continue;
            }
            vmpos = fp; vmlen = strlen(vsrch);
            top = hex ? (fp & ~15L) : Inicio_linea(fp);
            dtop = -1;
            continue;
        }
        if (hex)
        {
            switch (key)
            {
            case K_DOWN: if (top + 16 < size) top += 16; break;
            case K_UP:   top -= 16; break;
            case K_PGDN: if (top + 368 < size) top += 368; break;
            case K_PGUP: top -= 368; break;
            case K_HOME: top = 0; break;
            case K_END:  top = size > 368 ? ((size - 368 + 15) & ~15L) : 0; break;
            }
            if (top < 0) top = 0;
        } else {
            switch (key)
            {
            case K_DOWN: if (lo[1] < size) top = lo[1]; break;
            case K_UP:   top = Linea_Previa(top); break;
            case K_PGDN: if (lo[23] < size) top = lo[23]; break;
            case K_PGUP: for (k = 0; k < 23; k++) top = Linea_Previa(top); break;
            case K_HOME: top = 0; break;
            case K_END:  top = size; for (k = 0; k < 23; k++) top = Linea_Previa(top); break;
            }
        }
    }
    close(vfd);
    free(b);
    Forma_cursor(1);
}

static void visor(const char *fn)
{
    Visor_base(fn);
}

static unsigned tseg;
static unsigned long tcap, tlen, gs, ge;
static unsigned clipseg;
static unsigned long cliplen;

static unsigned char __far *LP(unsigned long ph)
{
    return (unsigned char __far *)MK_FP(tseg + (unsigned)(ph >> 4), (unsigned)(ph & 15));
}

static unsigned char GB(unsigned long p)
{
    return *LP(p < gs ? p : p + (ge - gs));
}

static void SB(unsigned long p, unsigned char v)
{
    *LP(p < gs ? p : p + (ge - gs)) = v;
}

static void mover_hex(unsigned long dst, unsigned long src, unsigned long n)
{
    unsigned m;
    if (dst < src)
    {
        while (n)
        {
            m = n > 0x7000UL ? 0x7000 : (unsigned)n;
            _fmemmove(LP(dst), LP(src), m);
            dst += m; src += m; n -= m;
        }
    } else {
        while (n) {
            m = n > 0x7000UL ? 0x7000 : (unsigned)n;
            n -= m;
            _fmemmove(LP(dst + n), LP(src + n), m);
        }
    }
}

static void ed_hacer_Hueco(unsigned long at) {
    unsigned long n;
    if (at == gs) return;
    if (at < gs)
    {
        n = gs - at;
        mover_hex(ge - n, at, n);
        gs = at;
        ge -= n;
    } else {
        n = at - gs;
        mover_hex(gs, ge, n);
        gs += n;
        ge += n;
    }
}

static void Leer_Rango(unsigned dseg, unsigned long pos, unsigned long n) {
    unsigned long done = 0, ph;
    unsigned m;
    while (done < n)
    {
        m = n - done > 0x7000UL ? 0x7000 : (unsigned)(n - done);
        if (pos < gs && pos + m > gs) m = (unsigned)(gs - pos);
        ph = pos < gs ? pos : pos + (ge - gs);
        _fmemcpy(MK_FP(dseg + (unsigned)(done >> 4), (unsigned)(done & 15)), LP(ph), m);
        pos += m;
        done += m;
    }
}

static void leer_Cerca(unsigned char *dst, unsigned long pos, unsigned n)
{
    unsigned m;
    while (n)
    {
        m = n;
        if (pos < gs && pos + m > gs) m = (unsigned)(gs - pos);
        _fmemcpy(dst, LP(pos < gs ? pos : pos + (ge - gs)), m);
        dst += m;
        pos += m;
        n -= m;
    }
}

static int Escribir_rango(int fd, unsigned long pos, unsigned long n) {
    unsigned long ph;
    unsigned m, w;
    while (n) {
        m = n > 0x7000UL ? 0x7000 : (unsigned)n;
        if (pos < gs && pos + m > gs) m = (unsigned)(gs - pos);
        ph = pos < gs ? pos : pos + (ge - gs);
        _dos_write(fd, LP(ph), m, &w);
        if (w != m) return 0;
        pos += m;
        n -= m;
    }
    return 1;
}

static unsigned long contar_Nl(unsigned long pa, unsigned long pb) {
    unsigned long c = 0;
    unsigned m, r;
    unsigned char __far *p;
    unsigned char __far *q;
    while (pa < pb) {
        m = pb - pa > 0x7000UL ? 0x7000 : (unsigned)(pb - pa);
        p = LP(pa);
        r = m;
        while (r && (q = (unsigned char __far *)_fmemchr(p, '\n', r)) != NULL) {
            c++;
            r -= (unsigned)(q - p) + 1;
            p = q + 1;
        }
        pa += m;
    }
    return c;
}

static unsigned long num_lineas(unsigned long a, unsigned long b) {
    unsigned long c = 0, m;
    if (a >= b) return 0;
    if (a < gs)
    {
        m = b < gs ? b : gs;
        c += contar_Nl(a, m);
    }
    if (b > gs)
    {
        m = a > gs ? a : gs;
        c += contar_Nl(m + (ge - gs), b + (ge - gs));
    }
    return c;
}

static unsigned Pedir_Mem_alta(unsigned paras) {
    union REGS r;
    unsigned strat, link, seg;
    int haslink;
    r.x.ax = 0x5800; intdos(&r, &r); strat = r.x.ax;
    r.x.ax = 0x5802; intdos(&r, &r); haslink = !r.x.cflag; link = r.h.al;
    if (haslink) { r.x.ax = 0x5803; r.x.bx = 1; intdos(&r, &r); }
    r.x.ax = 0x5801; r.x.bx = 0x82; intdos(&r, &r);
    if (r.x.cflag) { r.x.ax = 0x5801; r.x.bx = 2; intdos(&r, &r); }
    if (_dos_allocmem(paras, &seg)) seg = 0;
    r.x.ax = 0x5801; r.x.bx = strat; intdos(&r, &r);
    if (haslink) { r.x.ax = 0x5803; r.x.bx = link; intdos(&r, &r); }
    return seg;
}

static int poner_Portapapeles(unsigned long a, unsigned long n)
{
    unsigned seg;
    if (clipseg) { _dos_freemem(clipseg); clipseg = 0; cliplen = 0; }
    if (!n) return 1;
    if (n > 0xFFFF0UL) return 0;
    seg = Pedir_Mem_alta((unsigned)((n + 15) >> 4));
    if (!seg) return 0;
    Leer_Rango(seg, a, n);
    clipseg = seg;
    cliplen = n;
    return 1;
}

static unsigned long epos, etop, esa, ecpos, ecln, egoto;
static unsigned elcol, ewant;
static int esel, emod, ehex, enib, easc, eovr, ecx, ecy;
static char efn[90], edir[80], emsg[60], sfind[41], srepl[41], lastadd[80];

static const char *editkeys[10] = { "Help","Save","","Hex/Txt","Copy","Paste","Find","Insert","","Quit" };

static int ed_Hay_sitio(unsigned long add) {
    unsigned long gap = ge - gs, d, ncap;
    unsigned maxp;

    if (gap >= add) return 1;
    d = (add - gap + 16384UL + 15) & ~15UL;
    ncap = tcap + d;
    if (ncap > 0xFFFF0UL || _dos_setblock((unsigned)(ncap >> 4), tseg, &maxp)) {
        d = (add - gap + 15) & ~15UL;
        ncap = tcap + d;
        if (ncap > 0xFFFF0UL || _dos_setblock((unsigned)(ncap >> 4), tseg, &maxp)) return 0;
    }
    mover_hex(ge + d, ge, tcap - ge);
    ge += d;
    tcap = ncap;
    return 1;
}

static unsigned long ed_linea_de(unsigned long p)
{
    if (p >= ecpos) ecln += num_lineas(ecpos, p);
    else ecln -= num_lineas(p, ecpos);
    ecpos = p;
    return ecln;
}

static int ed_Insertar(unsigned long at, const unsigned char __far *s, unsigned long n)
{
    unsigned long done = 0, o;
    unsigned sseg, m;
    if (!n) return 1;
    if (!ed_Hay_sitio(n)) { strcpy(emsg, "Out of memory"); return 0; }
    ed_hacer_Hueco(at);
    sseg = FP_SEG(s) + (FP_OFF(s) >> 4);
    o = FP_OFF(s) & 15;
    while (done < n) {
        m = n - done > 0x7000UL ? 0x7000 : (unsigned)(n - done);
        _fmemcpy(LP(gs + done),
                 MK_FP(sseg + (unsigned)((o + done) >> 4), (unsigned)((o + done) & 15)), m);
        done += m;
    }
    gs += n;
    tlen += n;
    if (at < ecpos) { ecln += num_lineas(at, at + n); ecpos += n; }
    emod = 1;
    return 1;
}

static void ed_borrar(unsigned long at, unsigned long n) {
    if (at >= tlen) return;
    if (n > tlen - at) n = tlen - at;
    if (!n) return;
    if (at + n <= ecpos) { ecln -= num_lineas(at, at + n); ecpos -= n; }
    else if (at < ecpos) { ecln -= num_lineas(at, ecpos); ecpos = at; }
    ed_hacer_Hueco(at);
    ge += n;
    tlen -= n;
    emod = 1;
}

static unsigned char lbuf[128];
static unsigned char hxb[368];

static unsigned long ed_buscar_Nl(unsigned long p)
{
    unsigned m;
    unsigned char __far *q;
    unsigned char __far *f;
    while (p < tlen) {
        m = tlen - p > 0x7000UL ? 0x7000 : (unsigned)(tlen - p);
        if (p < gs && p + m > gs) m = (unsigned)(gs - p);
        q = LP(p < gs ? p : p + (ge - gs));
        f = (unsigned char __far *)_fmemchr(q, '\n', m);
        if (f) return p + (unsigned)(f - q);
        p += m;
    }
    return tlen;
}

static unsigned long ed_Ini_linea(unsigned long p)
{
    unsigned m, i;
    unsigned char __far *q;
    while (p > 0)
    {
        m = p > 0x7000UL ? 0x7000 : (unsigned)p;
        if (p > gs && p - m < gs) m = (unsigned)(p - gs);
        q = LP((p - m) < gs ? (p - m) : (p - m) + (ge - gs));
        for (i = m; i > 0; i--)
            if (q[i - 1] == '\n') return p - m + i;
        p -= m;
    }
    return 0;
}

static unsigned long ed_fin_linea(unsigned long p) {
    p = ed_buscar_Nl(p);
    if (p < tlen && p > 0 && GB(p - 1) == '\r') p--;
    return p;
}

static unsigned long Ed_sig_linea(unsigned long e)
{
    if (e < tlen && GB(e) == '\r' && e + 1 < tlen && GB(e + 1) == '\n') e++;
    if (e < tlen && GB(e) == '\n') e++;
    return e;
}

static unsigned ed_Col_De(unsigned long p)
{
    unsigned long s = ed_Ini_linea(p);
    unsigned c = 0, m, k;
    while (s < p)
    {
        m = p - s > 128 ? 128 : (unsigned)(p - s);
        leer_Cerca(lbuf, s, m);
        for (k = 0; k < m; k++) c = lbuf[k] == '\t' ? (c | 7) + 1 : c + 1;
        s += m;
    }
    return c;
}

static unsigned long Ed_Pos_En(unsigned long s, unsigned col)
{
    unsigned long e = ed_fin_linea(s);
    unsigned c = 0, n, m, k;
    while (s < e) {
        m = e - s > 128 ? 128 : (unsigned)(e - s);
        leer_Cerca(lbuf, s, m);
        for (k = 0; k < m; k++) {
            n = lbuf[k] == '\t' ? (c | 7) + 1 : c + 1;
            if (n > col) return s + k;
            c = n;
        }
        s += m;
    }
    return s;
}

static void Ed_arreglar_crlf(void)
{
    if (!ehex && epos > 0 && epos < tlen && GB(epos) == '\n' && GB(epos - 1) == '\r') epos--;
}

static void ed_Arriba(void)
{
    unsigned long s = ed_Ini_linea(epos);
    if (s) epos = Ed_Pos_En(ed_Ini_linea(s - 1), ewant);
}

static void ed_abajo(void)
{
    unsigned long e = ed_fin_linea(epos);
    if (e < tlen) epos = Ed_Pos_En(Ed_sig_linea(e), ewant);
}

static void Ed_ver_texto(void) {
    unsigned long q, e;
    unsigned r, c;
    if (etop > tlen) etop = tlen;
    etop = ed_Ini_linea(etop);
    if (epos < etop) etop = ed_Ini_linea(epos);
    else
    {
        q = etop;
        for (r = 0; r < 23; r++) {
            e = ed_fin_linea(q);
            if (epos <= e || e >= tlen) break;
            q = Ed_sig_linea(e);
        }
        if (r >= 23) {
            etop = ed_Ini_linea(epos);
            for (r = 0; r < 22 && etop > 0; r++) etop = ed_Ini_linea(etop - 1);
        }
    }
    c = ed_Col_De(epos);
    if (c < elcol) elcol = c;
    if (c >= elcol + 80) elcol = c - 79;
}

static void Ed_rango_Sel(unsigned long *a, unsigned long *b) {
    *a = esa < epos ? esa : epos;
    *b = esa < epos ? epos : esa;
}

static void Ed_dib_texto(void)
{
    unsigned long p, e, q, q2, smin = 0, smax = 0;
    unsigned cc, n, r, i, k, m;
    unsigned short __far *v;
    unsigned char ch;
    int a, done = 0, stop;

    if (esel) Ed_rango_Sel(&smin, &smax);
    p = etop;
    ecx = 0; ecy = 1;
    for (r = 0; r < 23; r++) {
        v = vid + (r + 1) * 80; vdirty = 1;
        for (i = 0; i < 80; i++) v[i] = ((unsigned)col[A_TXT] << 8) | ' ';
        if (done) continue;
        e = ed_fin_linea(p);
        cc = 0;
        q = p;
        stop = 0;
        while (q < e && !stop)
        {
            m = e - q > 128 ? 128 : (unsigned)(e - q);
            leer_Cerca(lbuf, q, m);
            for (k = 0; k < m; k++) {
                if (cc >= elcol + 80) { stop = 1; break; }
                q2 = q + k;
                if (q2 == epos) { ecx = cc - elcol; ecy = r + 1; }
                ch = lbuf[k];
                a = (esel && q2 >= smin && q2 < smax) ? A_CUR : A_TXT;
                n = ch == '\t' ? 8 - (cc & 7) : 1;
                if (ch == '\t') ch = ' ';
                while (n--)
                {
                    if (cc >= elcol && cc < elcol + 80) v[cc - elcol] = ((unsigned)col[a] << 8) | ch;
                    cc++;
                }
            }
            q += m;
        }
        if (!stop)
        {
            if (e == epos) { ecx = cc - elcol; ecy = r + 1; }

            if (esel && e < tlen && e >= smin && e < smax && cc >= elcol && cc < elcol + 80)
                v[cc - elcol] = ((unsigned)col[A_CUR] << 8) | ' ';
        }
        if (e >= tlen) done = 1;
        else p = Ed_sig_linea(e);
    }
}

static void Ed_Ver_hex(void) {
    if (epos < etop) etop = epos & ~15UL;
    if (epos >= etop + 368) etop = (epos & ~15UL) - 352;
    etop &= ~15UL;
}

static void Ed_Dib_Hex(void)
{
    static const char hx[] = "0123456789ABCDEF";
    unsigned long smin = 0, smax = 0, p, avail;
    unsigned r, i, n, hi, lo, at, a2, a, j;
    unsigned short __far *v;
    unsigned char b;

    if (esel) Ed_rango_Sel(&smin, &smax);
    avail = tlen > etop ? tlen - etop : 0;
    n = avail > 368 ? 368 : (unsigned)avail;
    leer_Cerca(hxb, etop, n);
    at = (unsigned)col[A_TXT] << 8;
    a2 = (unsigned)col[A_CUR] << 8;
    for (r = 0; r < 23; r++) {
        v = vid + (r + 1) * 80; vdirty = 1;
        for (i = 0; i < 80; i++) v[i] = at | ' ';
        if (r * 16 > n) continue;
        p = etop + (unsigned long)r * 16;
        hi = (unsigned)(p >> 16);
        lo = (unsigned)p;
        v[0] = at | hx[(hi >> 12) & 15]; v[1] = at | hx[(hi >> 8) & 15];
        v[2] = at | hx[(hi >> 4) & 15];  v[3] = at | hx[hi & 15];
        v[4] = at | hx[(lo >> 12) & 15]; v[5] = at | hx[(lo >> 8) & 15];
        v[6] = at | hx[(lo >> 4) & 15];  v[7] = at | hx[lo & 15];
        for (i = 0; i < 16; i++) {
            j = r * 16 + i;
            if (j >= n) break;
            b = hxb[j];
            a = (esel && p + i >= smin && p + i < smax) ? a2 : at;
            v[9 + i * 3] = a | hx[b >> 4];
            v[10 + i * 3] = a | hx[b & 15];
            v[58 + i] = a | (b ? b : '.');
        }
    }
    r = (unsigned)((epos - etop) / 16);
    i = (unsigned)(epos & 15);
    ecy = r + 1;
    ecx = easc ? 58 + i : 9 + i * 3 + enib;
}

static void ed_Dibujar(void)
{
    char t[100];
    const char *nm = strrchr(efn, '\\');
    nm = nm ? nm + 1 : efn;
    if (ehex)
    {
        Ed_Ver_hex();
        Ed_Dib_Hex();
        fmt(t, " %-12s Ofs %08lX  %lu bytes %s HEX %s", nm, epos, tlen,
            emod ? "*" : " ", easc ? "ASCII" : "");
    } else {
        Ed_ver_texto();
        Ed_dib_texto();
        fmt(t, " %-12s Lin %-5lu Col %-4u %lu bytes %s %s", nm, ed_linea_de(epos), ed_Col_De(epos) + 1,
            tlen, emod ? "*" : " ", eovr ? "OVR" : "INS");
    }
    poner_Txt(0, 0, A_KEYL, t, 80);
    if (emsg[0]) poner_Txt(79 - strlen(emsg), 0, A_KEYL, emsg, strlen(emsg));
    Dib_Teclas(editkeys);
    pos_cursor(ecx, ecy);
}

static long ed_Buscar(unsigned long from, const char *s) {
    unsigned n = strlen(s), m, j, i;
    unsigned long p = from, endp;
    int cu, cl, c;
    unsigned char __far *q;

    if (!n || n > tlen) return -1;
    cu = toupper((unsigned char)s[0]);
    cl = tolower((unsigned char)s[0]);
    endp = tlen - n + 1;
    while (p < endp) {
        m = endp - p > 0x7000UL ? 0x7000 : (unsigned)(endp - p);
        if (p < gs && p + m > gs) m = (unsigned)(gs - p);
        q = LP(p < gs ? p : p + (ge - gs));
        for (j = 0; j < m; j++) {
            c = q[j];
            if (c != cu && c != cl) continue;
            for (i = 1; i < n && toupper(GB(p + j + i)) == toupper((unsigned char)s[i]); i++) ;
            if (i == n) return (long)(p + j);
        }
        p += m;
    }
    return -1;
}

static void Ed_Buscar_sig(void) {
    long f;
    if (!sfind[0]) return;
    f = ed_Buscar(epos, sfind);
    if (f < 0) { strcpy(emsg, "Not found"); return; }
    esa = (unsigned long)f;
    epos = (unsigned long)f + strlen(sfind);
    esel = 1;
    ewant = ed_Col_De(epos);
}

static void ed_Cursor_arriba(void)
{
    int i;
    if (ehex) { etop = epos & ~15UL; etop = etop >= 48 ? etop - 48 : 0; return; }
    etop = ed_Ini_linea(epos);
    for (i = 0; i < 3 && etop > 0; i++) etop = ed_Ini_linea(etop - 1);
}

static void ed_reemplazar(void) {
    long f;
    unsigned n, rn;
    unsigned long from, cnt = 0;
    int all = 0, k;

    if (!pedir_Texto("Replace", "Find:", sfind, 40) || !sfind[0]) return;
    if (!pedir_Texto("Replace", "Replace with:", srepl, 40)) return;
    n = strlen(sfind);
    rn = strlen(srepl);
    from = epos;
    for (;;)
    {
        f = ed_Buscar(from, sfind);
        if (f < 0) break;
        esa = (unsigned long)f;
        epos = (unsigned long)f + n;
        esel = 1;
        if (!all) {
            ed_Cursor_arriba();
            ed_Dibujar();
            k = pedir_tecla("Replace", "Replace this one?", "Y = yes   N = no   A = all   Esc = stop", "YNA");
            if (k == 27) break;
            if (k == 'N') { from = (unsigned long)f + 1; continue; }
            if (k == 'A') all = 1;
        }
        ed_borrar((unsigned long)f, n);
        if (!ed_Insertar((unsigned long)f, (const unsigned char *)srepl, rn)) break;
        from = (unsigned long)f + rn;
        epos = from;
        cnt++;
    }
    esel = 0;
    ewant = ed_Col_De(epos);
    fmt(emsg, "%lu replacements", cnt);
}

static int Ed_Guardar(void)
{
    int fd, ok;
    fd = open(efn, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, S_IREAD | S_IWRITE);
    if (fd < 0) { Aviso("Error", "Cannot save (read-only?)"); return 0; }
    ok = Escribir_rango(fd, 0, tlen);
    close(fd);
    if (!ok) { Aviso("Error", "Write error (disk full?)"); return 0; }
    emod = 0;
    strcpy(emsg, "Saved");
    return 1;
}

static void Ed_anadir(void) {
    char fn[90];
    unsigned long s, e;
    unsigned char c = '\n';
    int fd;
    long sz;

    s = ed_Ini_linea(epos);
    e = ed_fin_linea(epos);
    if (!pedir_Texto("Append line to end of", "File:", lastadd, 78) || !lastadd[0]) return;
    ruta_Abs(fn, edir, lastadd);
    fd = open(fn, O_RDWR | O_BINARY);
    if (fd < 0) fd = open(fn, O_RDWR | O_CREAT | O_BINARY, S_IREAD | S_IWRITE);
    if (fd < 0) { strcpy(emsg, "Cannot open file"); return; }
    sz = lseek(fd, 0L, SEEK_END);
    if (sz > 0) {
        lseek(fd, sz - 1, SEEK_SET);
        if (read(fd, &c, 1) == 1 && c == 0x1A) {
            sz--;
            c = '\n';
            if (sz > 0) { lseek(fd, sz - 1, SEEK_SET); read(fd, &c, 1); }
        }
        lseek(fd, sz, SEEK_SET);
        if (c != '\n') write(fd, "\r\n", 2);
    }
    if (e > s) Escribir_rango(fd, s, e - s);
    write(fd, "\r\n", 2);
    close(fd);
    fmt(emsg, "Line added to %.36s", lastadd);
}

static void Ed_Borrar_Sel(void)
{
    unsigned long a, b;
    Ed_rango_Sel(&a, &b);
    ed_borrar(a, b - a);
    epos = a;
    esel = 0;
}

static void ed_copiar(void)
{
    unsigned long a, b;
    if (!esel) { strcpy(emsg, "Nothing selected"); return; }
    Ed_rango_Sel(&a, &b);
    if (poner_Portapapeles(a, b - a)) fmt(emsg, "Copied: %lu bytes", b - a);
    else strcpy(emsg, "Out of memory to copy");
}

static void Ed_Pegar(void)
{
    if (!clipseg) { strcpy(emsg, "Clipboard empty"); return; }
    if (ed_Insertar(epos, (unsigned char __far *)MK_FP(clipseg, 0), cliplen)) epos += cliplen;
    esel = 0;
}

static void ed_ayuda(void) {
    static const char *h[] = {
        "Arrows PgUp PgDn Home End    move",
        "Ctrl+Home / Ctrl+End         start / end of file",
        "Ctrl+Left / Ctrl+Right       previous / next word",
        "Shift + move                 select",
        "F5 copy   F6 paste           (what is selected with Shift)",
        "Ctrl+Ins Shift+Del Shift+Ins copy  cut  paste",
        "Ctrl+C calculator   Ctrl+P CD player",
        "Ctrl+Y or Ctrl+J             delete line",
        "Ctrl+I or F8                 append line to another file",
        "Ins                          insert / overwrite",
        "F2 save   F4 hex/text   Alt+F7 replace",
        "F7 find   Shift+F7 find next",
        "Esc or F10                   exit",
        "Hex: Tab switches hex/ASCII, Ins adds a byte, Del deletes",
        "The clipboard lasts until a program is run",
        0 };
    int i;
    Caja(9, 3, 62, 18, A_DLG, "Editor help");
    for (i = 0; h[i]; i++) poner_Txt(11, 5 + i, A_DLG, h[i], 58);
    Forma_cursor(0);
    Leer_Tecla();
    Forma_cursor(1);
}

static int ed_Tecla_Nav(unsigned k) {
    switch (k)
    {
    case K_UP: case K_DOWN: case K_LEFT: case K_RIGHT: case K_PGUP: case K_PGDN:
    case K_HOME: case K_END: case K_CHOME: case K_CEND: case K_CPGUP: case K_CPGDN:
    case K_CLEFT: case K_CRIGHT:
        return 1;
    }
    return 0;
}

static void ed_Mover_Texto(unsigned k) {
    int i;
    switch (k)
    {
    case K_LEFT:
        if (epos > 0) epos--;
        Ed_arreglar_crlf();
        break;
    case K_RIGHT:
        if (epos < tlen)
        {
            if (GB(epos) == '\r' && epos + 1 < tlen && GB(epos + 1) == '\n') epos += 2;
            else epos++;
        }
        break;
    case K_UP:   ed_Arriba(); return;
    case K_DOWN: ed_abajo(); return;
    case K_PGUP: for (i = 0; i < 22; i++) ed_Arriba(); return;
    case K_PGDN: for (i = 0; i < 22; i++) ed_abajo(); return;
    case K_HOME: epos = ed_Ini_linea(epos); break;
    case K_END:  epos = ed_fin_linea(epos); break;
    case K_CHOME: case K_CPGUP: epos = 0; break;
    case K_CEND: case K_CPGDN: epos = tlen; break;
    case K_CLEFT:
        while (epos > 0 && !isalnum(GB(epos - 1))) epos--;
        while (epos > 0 && isalnum(GB(epos - 1))) epos--;
        break;
    case K_CRIGHT:
        while (epos < tlen && isalnum(GB(epos))) epos++;
        while (epos < tlen && !isalnum(GB(epos))) epos++;
        Ed_arreglar_crlf();
        break;
    }
    ewant = ed_Col_De(epos);
}

static void ed_mover_hex(unsigned k)
{
    enib = 0;
    switch (k) {
    case K_LEFT:  if (epos > 0) epos--; break;
    case K_RIGHT: if (epos < tlen) epos++; break;
    case K_UP:    if (epos >= 16) epos -= 16; break;
    case K_DOWN:  if (epos + 16 <= tlen) epos += 16; break;
    case K_PGUP:  epos = epos >= 368 ? epos - 368 : 0; break;
    case K_PGDN:  epos = tlen - epos > 368 ? epos + 368 : tlen; break;
    case K_HOME:  epos &= ~15UL; break;
    case K_END:   epos |= 15; if (epos > tlen) epos = tlen; break;
    case K_CHOME: case K_CPGUP: case K_CLEFT:  epos = 0; break;
    case K_CEND: case K_CPGDN: case K_CRIGHT: epos = tlen; break;
    }
}

static int Digito_hex(int c)
{
    if (c >= '0' && c <= '9') return c - '0';
    c = toupper(c);
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

static void Editor_base(const char *fn, const char *dir) {
    int fd, sh, h, skipdraw = 0, hadmsg;
    long sz;
    unsigned k, c, paras, rd, m;
    unsigned long pos, need, s, e, n;
    unsigned char ch;
    char t[70];

    fd = open(fn, O_RDONLY | O_BINARY);
    if (fd < 0) { Aviso("Error", "Cannot open file"); return; }
    sz = lseek(fd, 0L, SEEK_END);
    need = (unsigned long)sz + 16384UL;
    if (need > 0xFFFF0UL) need = 0xFFFF0UL;
    if (need < (unsigned long)sz + 512UL)
    {
        close(fd);
        Aviso("Error", "File too big to edit (max 1 MB)");
        return;
    }
    paras = (unsigned)(need >> 4);
    if (_dos_allocmem(paras, &tseg))
    {

        paras = tseg;

        if ((unsigned long)paras * 16UL > (unsigned long)sz + 1024UL + 32768UL) paras -= 2048;
        if ((unsigned long)paras * 16UL < (unsigned long)sz + 1024UL)
        {
            close(fd);
            fmt(t, "Out of memory: %lu KB free", (unsigned long)paras / 64);
            Aviso("Error", t);
            return;
        }
        if (_dos_allocmem(paras, &tseg)) { close(fd); Aviso("Error", "Out of memory"); return; }
    }
    tcap = (unsigned long)paras << 4;
    lseek(fd, 0L, SEEK_SET);
    pos = 0;
    while (pos < (unsigned long)sz)
    {
        m = (unsigned long)sz - pos > 0x7000UL ? 0x7000 : (unsigned)((unsigned long)sz - pos);
        _dos_read(fd, LP(pos), m, &rd);
        if (!rd) break;
        pos += rd;
    }
    close(fd);
    tlen = pos;
    gs = tlen;
    ge = tcap;
    epos = etop = esa = 0;
    elcol = ewant = 0;
    ecpos = 0; ecln = 1;
    esel = emod = ehex = enib = easc = eovr = 0;
    emsg[0] = 0;
    for (pos = 0, k = 0; pos < tlen && pos < 512; pos++) if (GB(pos) == 0) k++;
    ehex = k > 0;
    strcpy(efn, fn);
    strcpy(edir, dir);
    if (egoto > 1 && !ehex) {
        unsigned long l;
        for (l = 1; l < egoto && epos < tlen; l++) epos = Ed_sig_linea(ed_fin_linea(epos));
        ewant = 0;
        ed_Cursor_arriba();
    }
    egoto = 0;
    Forma_cursor(1);

    for (;;)
    {
        if (!_bios_keybrd(_KEYBRD_READY) && !skipdraw) ed_Dibujar();
        skipdraw = 0;
        hadmsg = emsg[0];
        emsg[0] = 0;
        k = Leer_Tecla();
        sh = *(unsigned char __far *)MK_FP(0x40, 0x17) & 3;
        if (sh)
        {

            c = k & 0xFF;
            if ((k >> 8) >= 0x47 && (k >> 8) <= 0x53 && ((c >= '0' && c <= '9') || c == '.')) k &= 0xFF00;
        }
        if (ed_Tecla_Nav(k))
        {
            if (sh) { if (!esel) { esa = epos; esel = 1; } }
            else esel = 0;
            {
                unsigned long p0 = epos, t0 = etop, a0 = esa;
                int s0 = esel, n0 = enib;
                unsigned c0 = elcol;
                if (ehex) ed_mover_hex(k); else ed_Mover_Texto(k);

                if (epos == p0 && etop == t0 && esa == a0 && esel == s0 && enib == n0 &&
                    elcol == c0 && !hadmsg) skipdraw = 1;
            }
            vaciar_teclas();
            continue;
        }
        switch (k)
        {
        case K_ESC:
        case K_F10:
            if (emod) {
                c = pedir_tecla("Editor", "Save changes?", "Y = yes   N = no   Esc = keep editing", "YN");
                if (c == 27) break;
                if (c == 'Y' && !Ed_Guardar()) break;
            }
            _dos_freemem(tseg);
            return;
        case K_F1: ed_ayuda(); break;
        case K_F2: Ed_Guardar(); break;
        case K_F4:
            ehex ^= 1; enib = 0; easc = 0;
            Ed_arreglar_crlf();
            ewant = ed_Col_De(epos);
            break;
        case K_F7:
            if (pedir_Texto("Find", "Text:", sfind, 40)) Ed_Buscar_sig();
            break;
        case K_SF7: Ed_Buscar_sig(); break;
        case K_AF7: ed_reemplazar(); break;
        case K_F5: case K_CINS: ed_copiar(); break;
        case K_F6: Ed_Pegar(); ewant = ed_Col_De(epos); break;
        case K_INS:
            if (sh) { Ed_Pegar(); ewant = ed_Col_De(epos); }
            else if (ehex) { ch = 0; ed_Insertar(epos, &ch, 1); enib = 0; }
            else eovr ^= 1;
            break;
        case K_DEL:
            if (sh) { ed_copiar(); if (esel) Ed_Borrar_Sel(); }
            else if (esel) Ed_Borrar_Sel();
            else if (epos >= tlen) ;
            else if (!ehex && GB(epos) == '\r' && epos + 1 < tlen && GB(epos + 1) == '\n') ed_borrar(epos, 2);
            else ed_borrar(epos, 1);
            enib = 0;
            ewant = ed_Col_De(epos);
            break;
        case K_BS:
            if (esel) Ed_Borrar_Sel();
            else if (epos > 0) {
                if (!ehex && epos >= 2 && GB(epos - 1) == '\n' && GB(epos - 2) == '\r') { epos -= 2; ed_borrar(epos, 2); }
                else { epos--; ed_borrar(epos, 1); }
            }
            enib = 0;
            ewant = ed_Col_De(epos);
            break;
        case K_CTRLY:
        case K_CTRLJ:
            if (ehex) break;
            s = ed_Ini_linea(epos);
            e = Ed_sig_linea(ed_fin_linea(epos));
            ed_borrar(s, e - s);
            epos = s;
            esel = 0;
            ewant = ed_Col_De(epos);
            break;
        case K_CTRLI:
        case K_F8:
            if (!ehex) Ed_anadir();
            break;
        case K_ENTER:
            if (ehex) break;
            esel = 0;
            if (ed_Insertar(epos, (const unsigned char *)"\r\n", 2)) epos += 2;
            ewant = 0;
            break;
        case K_TAB:
            if (ehex) { easc ^= 1; enib = 0; break; }
            esel = 0;
            ch = '\t';
            if (ed_Insertar(epos, &ch, 1)) epos++;
            ewant = ed_Col_De(epos);
            break;
        default:
            c = k & 0xFF;
            if (c < 32) break;
            esel = 0;
            ch = (unsigned char)c;
            if (ehex) {
                if (!easc) {
                    h = Digito_hex(c);
                    if (h < 0) break;
                    if (epos == tlen) { ch = 0; if (!ed_Insertar(epos, &ch, 1)) break; }
                    if (enib) SB(epos, (unsigned char)((GB(epos) & 0xF0) | h));
                    else SB(epos, (unsigned char)((GB(epos) & 0x0F) | (h << 4)));
                    emod = 1;
                    if (enib) { enib = 0; epos++; } else enib = 1;
                } else {
                    if (epos == tlen) { if (!ed_Insertar(epos, &ch, 1)) break; }
                    else { SB(epos, ch); emod = 1; }
                    epos++;
                }
            } else {
                n = ed_fin_linea(epos);
                if (eovr && epos < n) { SB(epos, ch); emod = 1; epos++; }
                else if (ed_Insertar(epos, &ch, 1)) epos++;
                ewant = ed_Col_De(epos);
            }
            break;
        }
    }
}

static void editor(const char *fn, const char *dir) {
    Editor_base(fn, dir);
}

typedef struct {
    unsigned long line;
    char path[79];
    char text[45];
} RES;

#define MAXRES 400
static RES __far *res;
static unsigned nres, maxres, resseg;
static char fmask[41] = "*.*", ftext[41], fneedle[41];
static int fsub = 1, fstop;
static unsigned fnl, fll;
static unsigned long fnfiles;
static char fln[256];
static char *fbuf;
static unsigned char upt[256];

static void Anadir_Result(const char *path, unsigned long line, const char *text)
{
    RES __far *r;
    if (nres >= maxres) { fstop = 1; return; }
    r = res + nres;
    nres++;
    r->line = line;
    _fstrncpy(r->path, path, 78);
    r->path[78] = 0;
    _fstrncpy(r->text, text, 44);
    r->text[44] = 0;
}

static int buscar_Sin_mayus(void) {
    unsigned i, j, last;
    unsigned char c0 = (unsigned char)fneedle[0];
    if (fll < fnl) return 0;
    last = fll - fnl;
    for (i = 0; i <= last; i++) {
        if (upt[(unsigned char)fln[i]] != c0) continue;
        for (j = 1; j < fnl && upt[(unsigned char)fln[i + j]] == (unsigned char)fneedle[j]; j++) ;
        if (j == fnl) return 1;
    }
    return 0;
}

static int Lin_Fich(const char *path, unsigned long ln) {
    char sn[45];
    unsigned i = 0, j = 0;
    if (!buscar_Sin_mayus()) return 0;
    while (i < fll && (fln[i] == ' ' || fln[i] == '\t')) i++;
    while (i < fll && j < 44) { sn[j++] = fln[i] < 32 ? ' ' : fln[i]; i++; }
    sn[j] = 0;
    Anadir_Result(path, ln, sn);
    return 1;
}

static void buscar_Texto(const char *path)
{
    int fd, n, i, hits = 0;
    unsigned long ln = 1;
    unsigned char c;

    fd = open(path, O_RDONLY | O_BINARY);
    if (fd < 0) return;
    n = read(fd, fbuf, 4096);
    for (i = 0; i < n && i < 512; i++)
        if (!fbuf[i]) { close(fd); return; }
    fll = 0;
    while (n > 0 && hits < 50 && !fstop) {
        for (i = 0; i < n; i++) {
            c = (unsigned char)fbuf[i];
            if (c == '\n') {
                if (Lin_Fich(path, ln) && ++hits >= 50) break;
                ln++;
                fll = 0;
            } else if (c != '\r' && fll < 255) fln[fll++] = (char)c;
        }
        if (hits >= 50) break;
        if (hay_Esc()) { fstop = 2; break; }
        n = read(fd, fbuf, 4096);
    }
    if (n <= 0 && fll && hits < 50 && !fstop) Lin_Fich(path, ln);
    close(fd);
}

static char ftmp[60];
static char fdas[11], fdbs[11], fsgs[11], fsls[11];
static unsigned fda, fdb;
static unsigned long fsg, fsl;
static int Filtrar(const struct find_t *ft);

static void Buscar_Fich(int ls) {
    struct find_t ft;
    unsigned rc;

    if (ls > 0 && sp[ls - 1] != '\\') sp[ls++] = '\\';
    strcpy(sp + ls, "*.*");
    rc = _dos_findfirst(sp, ATTR_ALL, &ft);
    while (!rc && !fstop) {
        if (ft.attrib & _A_SUBDIR) {
            if (ft.name[0] != '.' && ls + 14 < PMAX) {
                strcpy(sp + ls, ft.name);
                if (!ftext[0] && !fda && !fdb && !fsg && !fsl && Coincide_mascara(fmask, ft.name)) Anadir_Result(sp, 0, "<DIR>");
                if (fsub) Buscar_Fich(strlen(sp));
            }
        } else if (Coincide_mascara(fmask, ft.name) && Filtrar(&ft) && ls + 14 < PMAX) {
            strcpy(sp + ls, ft.name);
            strlwr(sp + ls);
            fnfiles++;
            poner_Txt(12, 11, A_DLG, sp, 56);
            fmt(ftmp, "Files: %lu   Found: %u", fnfiles, nres);
            poner_Txt(12, 12, A_DLG, ftmp, 56);
            volcar_rapido();
            if (!ftext[0]) Anadir_Result(sp, 0, "");
            else buscar_Texto(sp);
            if (hay_Esc()) fstop = 2;
        }
        rc = _dos_findnext(&ft);
    }
}

static const char *reskeys[10] = { "","","View","Edit","","","","","","Quit" };

static void Ver_Resultados(void) {
    int cur = 0, top = 0, i, go = -1, full = 1;
    unsigned k;
    char b[100], path[80], txt[46], dir[80], nm[13];
    RES __far *r;

    Forma_cursor(0);
    for (;;) {
        if (full)
        {
            dib_todo();
            Forma_cursor(0);
            Caja(1, 1, 78, 22, A_DLG, "Found");
            full = 0;
        }
        if (!_bios_keybrd(_KEYBRD_READY)) {
            fmt(b, " %-5d of %-5u ", cur + 1, nres);
            poner_Txt(32, 1, A_DLG, b, 16);
            for (i = 0; i < 20; i++) {
                if (top + i < (int)nres)
                {
                    r = res + top + i;
                    _fstrcpy(path, r->path);
                    _fstrcpy(txt, r->text);
                    if (r->line) fmt(b, "%s:%lu  %s", path, r->line, txt);
                    else fmt(b, "%s  %s", path, txt);
                    poner_Txt(2, 2 + i, top + i == cur ? A_SELD : A_DLG, b, 76);
                } else poner_Txt(2, 2 + i, A_DLG, "", 76);
            }
            Dib_Teclas(reskeys);
        }
        k = Leer_Tecla();
        if (k == K_ESC || k == K_F10) break;
        switch (k) {
        case K_UP:   if (cur > 0) cur--; vaciar_teclas(); break;
        case K_DOWN: if (cur < (int)nres - 1) cur++; vaciar_teclas(); break;
        case K_PGUP: cur -= 19; if (cur < 0) cur = 0; vaciar_teclas(); break;
        case K_PGDN: cur += 19; if (cur >= (int)nres) cur = nres - 1; vaciar_teclas(); break;
        case K_HOME: cur = 0; break;
        case K_END:  cur = nres - 1; break;
        case K_ENTER: go = cur; break;
        case K_F3:
        case K_F4:
            r = res + cur;
            if (r->text[0] == '<') break;
            _fstrcpy(path, r->path);
            if (k == K_F3) visor(path);
            else
            {
                strcpy(dir, path);
                Quitar_Dir(dir, nm);
                egoto = r->line;
                if (ftext[0]) strcpy(sfind, ftext);
                editor(path, dir);
            }
            full = 1;
            break;
        }
        if (go >= 0) break;
        if (cur < top) top = cur;
        if (cur >= top + 20) top = cur - 19;
    }
    Forma_cursor(1);
    refrescar(act ^ 1);
    if (go >= 0) {
        r = res + go;
        _fstrcpy(path, r->path);
        strcpy(dir, path);
        Quitar_Dir(dir, nm);
        cambiar_panel(&pan[act], dir, nm);
    } else refrescar(act);
}

static unsigned Leer_fecha(const char *p) {
    unsigned v[3];
    int n = 0, in = 0;
    v[0] = v[1] = v[2] = 0;
    for (; *p; p++) {
        if (*p >= '0' && *p <= '9') {
            if (n > 2) return 0;
            v[n] = v[n] * 10 + (unsigned)(*p - '0');
            in = 1;
        } else if (in) { n++; in = 0; }
    }
    if (in) n++;
    if (n != 3 || !v[0] || v[0] > 31 || !v[1] || v[1] > 12) return 0;
    if (v[2] < 80) v[2] += 2000;
    else if (v[2] < 100) v[2] += 1900;
    if (v[2] < 1980 || v[2] > 2107) return 0;
    return ((v[2] - 1980) << 9) | (v[1] << 5) | v[0];
}

static unsigned long Leer_num(const char *p) {
    unsigned long v = 0;
    for (; *p; p++) if (*p >= '0' && *p <= '9') v = v * 10 + (unsigned)(*p - '0');
    return v;
}

static int Filtrar(const struct find_t *ft) {
    if (fda && ft->wr_date < fda) return 0;
    if (fdb && ft->wr_date > fdb) return 0;
    if (fsg && ft->size <= fsg) return 0;
    if (fsl && ft->size >= fsl) return 0;
    return 1;
}

static int Buscar_Forma(void)
{
    static const char *lab[6] = { "Name or mask", "Contains (text)", "Date from",
                                  "Date to", "More than (bytes)", "Less than (bytes)" };
    static const int fw[6] = { 38, 38, 12, 12, 12, 12 };
    static const int fm[6] = { 40, 40, 10, 10, 10, 10 };
    static const int fr[6] = { 2, 4, 6, 7, 8, 9 };
    char *fb[6];
    int x = 8, y = 4, w = 64, h = 16, f = 0, c, l, i;
    unsigned k;
    char *b;
    fb[0] = fmask; fb[1] = ftext; fb[2] = fdas; fb[3] = fdbs; fb[4] = fsgs; fb[5] = fsls;
    Forma_cursor(0);
    for (;;)
    {
        Caja(x, y, w, h, A_DLG, "Find files");
        for (i = 0; i < 6; i++) {
            l = strlen(fb[i]);
            poner_Txt(x + 2, y + fr[i], A_DLG, lab[i], 18);
            poner_car(x + 21, y + fr[i], A_DLG, '[');
            poner_Txt(x + 22, y + fr[i], A_INP, fb[i] + (l > fw[i] ? l - fw[i] : 0), fw[i]);
            poner_car(x + 22 + fw[i], y + fr[i], A_DLG, ']');
        }
        poner_Txt(x + 36, y + 6, A_DLG, "dd/mm/yyyy", 12);
        poner_Txt(x + 36, y + 7, A_DLG, "dd/mm/yyyy", 12);
        poner_Txt(x + 2, y + 11, f == 6 ? A_SELD : A_DLG,
               fsub ? "[x] Search subdirectories" : "[ ] Search subdirectories", 28);
        button(x + 16, y + 13, "   Find   ", f == 7);
        button(x + 34, y + 13, " Cancel ", f == 8);
        if (f < 6) {
            l = strlen(fb[f]);
            pos_cursor(x + 22 + (l > fw[f] ? fw[f] : l), y + fr[f]);
            Forma_cursor(1);
        } else Forma_cursor(0);
        k = Leer_Tecla();
        c = k & 0xFF;
        if (k == K_ESC) { Forma_cursor(1); return 0; }
        if (k == K_DOWN || c == 9) f = (f + 1) % 9;
        else if (k == K_UP || k == 0x0F00) f = (f + 8) % 9;
        else if (k == K_ENTER || c == 13) {
            if (f == 8) { Forma_cursor(1); return 0; }
            if (f == 6) fsub = !fsub;
            else break;
        } else if (f == 6 && c == ' ') fsub = !fsub;
        else if (f < 6)
        {
            b = fb[f];
            l = strlen(b);
            if (c == 8) { if (l) b[l - 1] = 0; }
            else if (c >= 32 && l < fm[f]) { b[l] = (char)c; b[l + 1] = 0; }
        }
    }
    Forma_cursor(1);
    return 1;
}

static void hacer_Buscar(void) {
    char t[60];
    unsigned paras, i;

    if (!Buscar_Forma()) return;
    if (!fmask[0]) strcpy(fmask, "*.*");
    fda = Leer_fecha(fdas); fdb = Leer_fecha(fdbs);
    fsg = Leer_num(fsgs); fsl = Leer_num(fsls);

    fbuf = (char *)malloc(4096);
    if (!fbuf) { Aviso("Error", "Out of memory"); return; }
    maxres = MAXRES;
    for (;;) {
        paras = (unsigned)(((unsigned long)maxres * sizeof(RES) + 15) >> 4);
        resseg = Pedir_Mem_alta(paras);
        if (resseg) break;
        maxres >>= 1;
        if (maxres < 8) { free(fbuf); Aviso("Error", "Out of memory"); return; }
    }
    res = (RES __far *)MK_FP(resseg, 0);
    nres = 0; fstop = 0; fnfiles = 0;
    for (i = 0; i < 256; i++) upt[i] = (unsigned char)toupper(i);
    fnl = strlen(ftext);
    for (i = 0; i < fnl; i++) fneedle[i] = (char)upt[(unsigned char)ftext[i]];
    fneedle[fnl] = 0;

    Caja(10, 9, 60, 6, A_DLG, "Searching");
    fmt(t, "%s  %s%s", fmask, ftext[0] ? "text: " : "", ftext);
    poner_Txt(12, 10, A_DLG, t, 56);
    poner_Txt(12, 13, A_DLG, "Esc = cancel", 56);
    volcar_rapido();
    Forma_cursor(0);
    strcpy(sp, pan[act].path);
    Buscar_Fich(strlen(sp));
    free(fbuf);
    Forma_cursor(1);

    if (!nres) Aviso("Find", fstop == 2 ? "Search cancelled" : "Nothing found");
    else {
        if (fstop == 1) {
            fmt(t, "Too many results: showing the first %u", nres);
            Aviso("Find", t);
        }
        Ver_Resultados();
    }
    _dos_freemem(resseg);
}

#pragma pack(1)
typedef struct {
    unsigned char len, unit, cmd;
    unsigned status;
    unsigned char res[8];
    unsigned char media;
    unsigned long addr;
    unsigned long num;
    unsigned long vol;
} CDREQ;
#pragma pack()

static unsigned cddrv;
static int cdfirst, cdlast, cdsel, cdbin, cdvol = 200, cdntr;
static unsigned long cdend;
static unsigned long *cdts;
static unsigned char *cdtc;

static unsigned Cd_Peticion(CDREQ *rq)
{
    union REGS r;
    struct SREGS sr;
    segread(&sr);
    sr.es = sr.ds;
    r.x.ax = 0x1510;
    r.x.cx = cddrv;
    r.x.bx = (unsigned)rq;
    int86x(0x2F, &r, &r, &sr);
    return rq->status;
}

static unsigned Cd_control(int out, unsigned char *cb, unsigned n)
{
    CDREQ rq;
    memset(&rq, 0, sizeof rq);
    rq.len = 26;
    rq.cmd = out ? 12 : 3;
    rq.addr = (unsigned long)(void __far *)cb;
    rq.num = n;
    return Cd_Peticion(&rq);
}

static void cd_Simple(int cmd) {
    CDREQ rq;
    memset(&rq, 0, sizeof rq);
    rq.len = 13;
    rq.cmd = (unsigned char)cmd;
    Cd_Peticion(&rq);
}

static long hsg(const unsigned char *a)
{
    return ((long)a[2] * 60 + a[1]) * 75 + a[0] - 150;
}

static int Cd_audio(int t) {
    return !(cdtc[t] & 0x40);
}

static int Cd_pistas(void) {
    unsigned char cb[8];
    int t;
    cb[0] = 10;
    if (Cd_control(0, cb, 7) & 0x8000) return 0;
    cdfirst = cb[1];
    cdlast = cb[2];
    if (cdfirst < 1 || cdlast > 99 || cdlast < cdfirst) return 0;
    cdend = hsg(cb + 3);
    for (t = cdfirst; t <= cdlast; t++) {
        cb[0] = 11;
        cb[1] = (unsigned char)t;
        if (Cd_control(0, cb, 7) & 0x8000) return 0;
        cdts[t] = hsg(cb + 2);
        cdtc[t] = cb[6];
    }
    return cdlast - cdfirst + 1;
}

static void Cd_Tocar(int t)
{
    CDREQ rq;
    memset(&rq, 0, sizeof rq);
    rq.len = 22;
    rq.cmd = 132;
    rq.media = 0;
    rq.addr = cdts[t];
    rq.num = cdend - cdts[t];
    Cd_Peticion(&rq);
}

static void cd_Volumen(void) {
    unsigned char cb[9];
    cb[0] = 3;
    cb[1] = 0; cb[2] = (unsigned char)cdvol;
    cb[3] = 1; cb[4] = (unsigned char)cdvol;
    cb[5] = 2; cb[6] = 0;
    cb[7] = 3; cb[8] = 0;
    Cd_control(1, cb, 9);
}

static int cd_paso(int d)
{
    int t = cdsel, n = cdntr;
    while (n--)
    {
        t += d;
        if (t > cdlast) t = cdfirst;
        if (t < cdfirst) t = cdlast;
        if (Cd_audio(t)) return t;
    }
    return cdsel;
}

static int bcd_Ok(unsigned char b)
{
    return (b >> 4) < 10 && (b & 15) < 10;
}

static int cd_valor(unsigned char b) {
    if (!bcd_Ok(b)) { cdbin = 1; return b; }
    return cdbin ? b : (b >> 4) * 10 + (b & 15);
}

static int cd_Pista(unsigned char b)
{

    int bin = b, bcd = bcd_Ok(b) ? (b >> 4) * 10 + (b & 15) : -1;
    int vb = bin >= cdfirst && bin <= cdlast, vd = bcd >= cdfirst && bcd <= cdlast;
    if (vb && vd && bin != bcd)
        return abs(bin - cdsel) <= abs(bcd - cdsel) ? bin : bcd;
    if (vb) return bin;
    if (vd) return bcd;
    return bin;
}

static unsigned Cd_Tecla(void) {
    unsigned __far *tick = (unsigned __far *)MK_FP(0x40, 0x6C);
    unsigned last = *tick;
    Volcar();
    while (!_bios_keybrd(_KEYBRD_READY))
        if (*tick - last >= 18) return 0;
    return Norm_Tecla(_bios_keybrd(_KEYBRD_READ));
}

#define BF "\xDB"
#define BU "\xDF"
#define BD "\xDC"
static void Cd_Grande(int x, int y, int d, int a) {
    static const char *sg[10][3] = {
        { BF BU BF, BF " " BF, BF BD BF },
        { " " BD BF, "  " BF, "  " BF },
        { BU BU BF, " " BD BU, BF BD BD },
        { BU BU BF, " " BU BF, BD BD BF },
        { BF " " BF, BF BD BF, "  " BF },
        { BF BU BU, BU BU BF, BD BD BF },
        { BF BU BU, BF BU BF, BF BD BF },
        { BU BU BF, "  " BF, "  " BF },
        { BF BU BF, BF BU BF, BF BD BF },
        { BF BU BF, BU BU BF, BD BD BF } };
    poner_Txt(x, y, a, sg[d][0], 3);
    poner_Txt(x, y + 1, a, sg[d][1], 3);
    poner_Txt(x, y + 2, a, sg[d][2], 3);
}

static void cd_Boton(int x, int y, const char *g, int focus)
{
    char b[8];
    int l = strlen(g), w = (l & 1) ? 5 : 6, p = (w - l) / 2, i;
    for (i = 0; i < w; i++) b[i] = ' ';
    b[w] = 0;
    memcpy(b + p, g, l);
    Boton(x, y, b, focus, A_DLG);
}

static void Cd_Cabecera(int x, int y, const char *g) {
    char b[8];
    int l = strlen(g), p = (7 - l) / 2, i;
    for (i = 0; i < 7; i++) b[i] = ' ';
    b[7] = 0;
    memcpy(b + p, g, l);
    poner_Txt(x, y, A_DLG, b, 7);
}

static void Repro_cd(void)
{
    int x = 13, y = 2, w = 54, h = 18, r, c, i, n;
    int lx, blink = 0, dg, mm;
    int playing, paused, err, trk = 0, mn = 0, sc = 0, done = 0;
    int hold = 0, ix = 15, iw = 50, tl, sym;
    const char *lab;
    unsigned short *sv;
    unsigned k, st, cx, dx;
    unsigned char cb[12];
    union REGS rg;
    char t[60], tt[12], bar[24];
    unsigned long tot;

    if (incd) return;
    incd = 1;
    rg.h.ah = 3; rg.h.bh = 0;
    int86(0x10, &rg, &rg);
    cx = rg.x.cx; dx = rg.x.dx;
    sv = popbuf;
    cdts = cdts_s;
    cdtc = cdtc_s;
    for (r = 0; r <= h; r++)
        for (c = 0; c < w + 2; c++) sv[r * (w + 2) + c] = vid[(y + r) * 80 + x + c];
    Forma_cursor(0);
    Caja(x, y, w, h, A_DLG, "CD Player");

    rg.x.ax = 0x1500; rg.x.bx = 0;
    int86(0x2F, &rg, &rg);
    if (rg.x.bx == 0) {
        poner_Txt(x + 2, y + 1, A_DLG, "MSCDEX is not loaded (CD driver).", w - 4);
        poner_Txt(x + 2, y + 3, A_DLG, "Load MSCDEX or SHSUCDX and try again.", w - 4);
        poner_Txt(x + 2, y + 7, A_DLG, "Press a key", w - 4);
        do k = Cd_Tecla(); while (!k);
        done = 1;
    } else {
        cddrv = rg.x.cx;
        cdntr = 0;
        cdsel = 0;
        cb[0] = 4;
        if (!(Cd_control(0, cb, 9) & 0x8000)) cdvol = cb[2];
    }

    while (!done)
    {
        if (!cdntr) {
            cdntr = Cd_pistas();
            if (cdntr)
            {
                for (i = cdfirst; i <= cdlast; i++) if (Cd_audio(i)) break;
                cdsel = i > cdlast ? cdfirst : i;
            }
        }
        cb[0] = 15;
        st = Cd_control(0, cb, 11);
        err = (st & 0x8000) != 0;
        playing = !err && (st & 0x200) != 0;
        paused = !err && !playing && (cb[1] & 1);
        if (cdntr && (playing || paused)) {
            cb[0] = 12;
            if (!(Cd_control(0, cb, 11) & 0x8000)) {
                trk = cd_Pista(cb[2]);
                mn = cd_valor(cb[4]);
                sc = cd_valor(cb[5]);
                if (hold) hold--;
                else if (trk >= cdfirst && trk <= cdlast) cdsel = trk;
            }
        }
        blink ^= 1;
        lx = ix + 3;

        for (r = 2; r <= 9; r++) linea_H(ix, y + r - 1, iw, A_LCD, ' ');
        poner_car(ix, y + 1, A_LCDB, 0xDA); linea_H(ix + 1, y + 1, iw - 2, A_LCDB, 0xC4); poner_car(ix + iw - 1, y + 1, A_LCDB, 0xBF);
        for (r = 3; r <= 8; r++) { poner_car(ix, y + r - 1, A_LCDB, 0xB3); poner_car(ix + iw - 1, y + r - 1, A_LCDB, 0xB3); }
        poner_car(ix, y + 8, A_LCDB, 0xC0); linea_H(ix + 1, y + 8, iw - 2, A_LCDB, 0xC4); poner_car(ix + iw - 1, y + 8, A_LCDB, 0xD9);
        poner_Txt(x + 2, y + 9, A_DLG, "", w - 4);
        if (!cdntr) {
            poner_Txt(lx + 8, y + 3, A_LCD, err ? "NO DISC" : "NOT AUDIO", 14);
            poner_Txt(lx + 8, y + 5, A_LCDD, "Insert an audio CD", 24);
            poner_Txt(x + 2, y + 10, A_DLG, "", w - 4);
            for (r = 12; r <= 14; r++) poner_Txt(x + 2, y + r - 1, A_DLG, "", w - 4);
        } else {
            tot = cdend / 75;
            tl = (int)((cdsel < cdlast ? cdts[cdsel + 1] : cdend) - cdts[cdsel]) / 75;
            poner_Txt(lx, y + 2, A_LCDD, "TRACK", 5);
            poner_Txt(lx + 9, y + 2, A_LCDD, "TIME", 6);
            poner_Txt(lx + 30, y + 2, A_LCDD, "STATUS", 6);
            Cd_Grande(lx, y + 3, cdsel / 10 % 10, A_LCD);
            Cd_Grande(lx + 4, y + 3, cdsel % 10, A_LCD);
            mm = (playing || paused) ? mn : 0;
            if (mm > 99) mm = 99;
            dg = (playing || (paused && blink)) ? A_LCD : A_LCDD;
            Cd_Grande(lx + 9, y + 3, mm / 10, dg);
            Cd_Grande(lx + 13, y + 3, mm % 10, dg);
            poner_car(lx + 17, y + 3, dg, 0xFE);
            poner_car(lx + 17, y + 5, dg, 0xFE);
            Cd_Grande(lx + 19, y + 3, ((playing || paused) ? sc : 0) / 10 % 10, dg);
            Cd_Grande(lx + 23, y + 3, ((playing || paused) ? sc : 0) % 10, dg);
            fmt(t, "%c %s", playing ? 0x10 : paused ? 0xBA : 0xFE,
                playing ? "PLAYING" : paused ? "PAUSED" : "STOPPED");
            poner_Txt(lx + 30, y + 3, A_LCD, t, 15);
            fmt(t, "Track %d of %d", cdsel, cdlast);
            poner_Txt(lx + 30, y + 4, A_LCDD, t, 15);
            fmt(t, "Disc %d:%02d", (int)(tot / 60), (int)(tot % 60));
            poner_Txt(lx + 30, y + 5, A_LCDD, t, 15);

            n = 0;
            if ((playing || paused) && tl > 0) n = (mn * 60 + sc) * 44 / tl;
            if (n > 44) n = 44;
            for (i = 0; i < 44; i++) poner_car(lx + i, y + 7, i < n ? A_LCD : A_LCDD, i < n ? 0xDB : 0xB0);

            n = cdvol * 30 / 255;
            poner_Txt(x + 2, y + 10, A_DLG, " Volume", 8);
            for (i = 0; i < 30; i++) poner_car(x + 10 + i, y + 10, A_DLG, i < n ? 0xDB : 0xB0);
            fmt(t, " %3d%%", cdvol * 100 / 255);
            poner_Txt(x + 40, y + 10, A_DLG, t, w - 42);

            for (i = 0; i < 32; i++) {
                int tn = i + 1, cx0 = x + 3 + (i % 16) * 3, cy0 = y + 12 + i / 16;
                if (tn >= cdfirst && tn <= cdlast) {
                    if (Cd_audio(tn)) fmt(t, " %02d", tn); else strcpy(t, " --");
                    poner_Txt(cx0, cy0, tn == cdsel ? A_SELD : A_DLG, t, 3);
                } else poner_Txt(cx0, cy0, A_DLG, "", 3);
            }
        }

        poner_Txt(x + 2, y + 11, A_DLG, "", w - 4);
        for (r = 15; r <= 17; r++) poner_Txt(x + 2, y + r - 1, A_DLG, "", w - 4);
        cd_Boton(x + 3, y + 15, "\x11\x11", 0);
        cd_Boton(x + 11, y + 15, "\x10", playing);
        cd_Boton(x + 19, y + 15, "\xFE\xFE", paused);
        cd_Boton(x + 27, y + 15, "\xFE", cdntr && !playing && !paused);
        cd_Boton(x + 35, y + 15, "\x10\x10", 0);
        cd_Boton(x + 43, y + 15, "\x1E", 0);

        k = Cd_Tecla();
        if (!k) continue;
        c = (k & 0xFF) ? toupper(k & 0xFF) : 0;
        if (k == K_ESC) done = 1;
        else if (c == ' ' || c == 'P') {
            if (playing) cd_Simple(133);
            else if (paused) cd_Simple(136);
            else if (cdntr) Cd_Tocar(cdsel);
        } else if (k == K_ENTER) {
            if (playing || paused) { cd_Simple(133); cd_Simple(133); }
            else if (cdntr) Cd_Tocar(cdsel);
        }
        else if (k == K_LEFT || k == K_RIGHT || k == K_PGUP || k == K_PGDN) {
            if (cdntr) {
                cdsel = cd_paso((k == K_RIGHT || k == K_PGDN) ? 1 : -1);
                if (playing || paused) { cd_Simple(133); cd_Simple(133); Cd_Tocar(cdsel); hold = 2; }
            }
        } else if (c >= '1' && c <= '9') {
            if (cdntr && c - '0' >= cdfirst && c - '0' <= cdlast && Cd_audio(c - '0')) {
                cdsel = c - '0';
                cd_Simple(133); cd_Simple(133); Cd_Tocar(cdsel); hold = 2;
            }
        } else if (k == K_UP || k == K_DOWN || c == '+' || c == '-' || c == '=') {
            cdvol += (k == K_UP || c == '+' || c == '=') ? 16 : -16;
            if (cdvol > 255) cdvol = 255;
            if (cdvol < 0) cdvol = 0;
            cd_Volumen();
        } else if (c == 'E') {
            cb[0] = 0; Cd_control(1, cb, 1);
            cdntr = 0;
        } else if (c == 'C') {
            cb[0] = 5; Cd_control(1, cb, 1);
            cdntr = 0;
        }
    }

    vdirty = 1;
    for (r = 0; r <= h; r++)
        for (c = 0; c < w + 2; c++) vid[(y + r) * 80 + x + c] = sv[r * (w + 2) + c];
    Volcar();
    rg.h.ah = 1; rg.x.cx = cx;
    int86(0x10, &rg, &rg);
    rg.h.ah = 2; rg.h.bh = 0; rg.x.dx = dx;
    int86(0x10, &rg, &rg);
    incd = 0;
}

#define PGMAX 100
#define PGLEN 72

static void esperar_ds(int n)
{
    volatile unsigned __far *tick = (volatile unsigned __far *)MK_FP(0x40, 0x6C);
    unsigned last = *tick;
    unsigned t = (unsigned)(n * 18 / 10);
    while ((unsigned)(*tick - last) < t) { }
}

static void cd_Refrescar(void) {
    union REGS rg;
    unsigned char cb[8];
    unsigned first;
    int nd, i, r;

    rg.x.ax = 0x1500; rg.x.bx = 0;
    int86(0x2F, &rg, &rg);
    if (!rg.x.bx) return;
    nd = rg.x.bx;
    first = rg.x.cx;
    esperar_ds(8);
    for (r = 0; r < 3; r++) {
        for (i = 0; i < nd; i++) {
            cddrv = first + i;
            cb[0] = 2; Cd_control(1, cb, 1);
            cb[0] = 9; cb[1] = 0; Cd_control(0, cb, 2);
        }
        esperar_ds(5);
    }
}

static void Pg_Ejecutar(const char *args, char *tmp)
{
    char c[200];
    unir_ruta(tmp, extdir[0] ? extdir : ".", "NCPGUS.TMP");
    unir_ruta(c, extdir, "PGUSINIT.EXE");
    if (!extdir[0] || !existe(c)) strcpy(c, "PGUSINIT.EXE");
    strcat(c, " ");
    strcat(c, args);
    strcat(c, " > ");
    strcat(c, tmp);
    _nheapshrink();
    system(c);
    vdirty = 1;
    Volcar();
    Forma_cursor(0);
}

static void Pg_Lista_Cd(void)
{
    char (*ln)[PGLEN], tmp[100], b[PGLEN + 8], *q;
    int *num, n = 0, i, c, top = 0, cur = 0, rows = 17, go = -1, len;
    unsigned k;
    long v;
    int fd;
    char *buf;

    ln = (char (*)[PGLEN])malloc(PGMAX * PGLEN);
    num = (int *)malloc(PGMAX * sizeof(int));
    buf = (char *)malloc(4096);
    if (!ln || !num || !buf) { free(ln); free(num); free(buf); Aviso("Error", "Out of memory"); return; }
    Pg_Ejecutar("/cdlist", tmp);
    fd = open(tmp, O_RDONLY | O_BINARY);
    len = 0;
    if (fd >= 0) { len = read(fd, buf, 4095); close(fd); if (len < 0) len = 0; }
    remove(tmp);
    buf[len] = 0;
    q = buf;
    while (*q && n < PGMAX)
    {
        i = 0;
        while (*q && *q != '\n') {
            c = (unsigned char)*q++;
            if (c == '\t') c = ' ';
            if (c >= 32 && i < PGLEN - 1) ln[n][i++] = (char)c;
        }
        if (*q) q++;
        while (i && ln[n][i - 1] == ' ') i--;
        ln[n][i] = 0;
        if (!i) continue;

        b[0] = 0;
        i = 0;
        while (ln[n][i] == ' ' || ln[n][i] == '[' || ln[n][i] == '#') i++;
        num[n] = -1;
        if (ln[n][i] >= '0' && ln[n][i] <= '9') {
            v = 0;
            while (ln[n][i] >= '0' && ln[n][i] <= '9' && v < 9999) v = v * 10 + ln[n][i++] - '0';
            if (!isalpha((unsigned char)ln[n][i])) num[n] = (int)v;
        }
        n++;
    }
    free(buf);
    if (!n) {
        Aviso("PicoGUS", "PGUSINIT /cdlist returned no list");
        free(ln); free(num);
        return;
    }
    for (cur = 0; cur < n && num[cur] < 0; cur++) ;
    if (cur >= n) cur = 0;
    for (;;)
    {
        Caja(3, 1, 74, rows + 5, A_DLG, "PicoGUS CD-Rom List");
        for (i = 0; i < rows; i++) {
            if (top + i < n)
            {
                fmt(b, " %s", ln[top + i]);
                poner_Txt(4, 3 + i, top + i == cur ? A_SELD : A_DLG, b, 72);
            } else poner_Txt(4, 3 + i, A_DLG, "", 72);
        }
        poner_Txt(4, rows + 4, A_DLG, " Enter = load CD   Esc = close", 72);
        k = Leer_Tecla();
        if (k == K_ESC || k == K_F2 || k == K_F10) break;
        if (k == K_UP) { if (cur) cur--; }
        else if (k == K_DOWN) { if (cur < n - 1) cur++; }
        else if (k == K_PGUP) { cur -= rows; if (cur < 0) cur = 0; }
        else if (k == K_PGDN) { cur += rows; if (cur >= n) cur = n - 1; }
        else if (k == K_HOME) cur = 0;
        else if (k == K_END) cur = n - 1;
        else if (k == K_ENTER) { if (num[cur] >= 0) { go = num[cur]; break; } }
        if (cur < top) top = cur;
        if (cur >= top + rows) top = cur - rows + 1;
    }
    free(ln); free(num);
    Forma_cursor(1);
    if (go >= 0) {
        fmt(b, "/cdload %d", go);
        Pg_Ejecutar(b, tmp);
        refrescar(0);
        refrescar(1);
        remove(tmp);
        Forma_cursor(1);
    }
}

static void Menu_f2(void)
{
    unsigned k;
    int f = 0;
    Forma_cursor(0);
    for (;;)
    {
        Caja(20, 4, 40, 6, A_DLG, "Menu F2");
        poner_Txt(22, 6, f == 0 ? A_SELD : A_DLG, " F2 - PicoGUS CD-Rom List", 36);
        poner_Txt(22, 7, f == 1 ? A_SELD : A_DLG, " Refresh CD drive", 36);
        k = Leer_Tecla();
        if (k == K_ESC || k == K_F10) break;
        if (k == K_UP || k == K_DOWN) f ^= 1;
        else if (k == K_F2) { Pg_Lista_Cd(); break; }
        else if (k == K_ENTER) {
            if (f == 0) Pg_Lista_Cd();
            else { cd_Refrescar(); refrescar(0); refrescar(1); }
            break;
        }
    }
    Forma_cursor(1);
}

static int letra_alt(unsigned k) {
    static const char r1[] = "QWERTYUIOP", r2[] = "ASDFGHJKL", r3[] = "ZXCVBNM";
    unsigned sc = k >> 8;
    if (k & 0xFF) return 0;
    if (sc >= 0x10 && sc <= 0x19) return r1[sc - 0x10];
    if (sc >= 0x1E && sc <= 0x26) return r2[sc - 0x1E];
    if (sc >= 0x2C && sc <= 0x32) return r3[sc - 0x2C];
    if (sc >= 0x78 && sc <= 0x80) return '1' + (sc - 0x78);
    if (sc == 0x81) return '0';
    return 0;
}

static void Busqueda_rapida(PANEL *p)
{
    int i, j;
    for (j = 0; j < p->n; j++) {
        i = (p->cur + j) % p->n;
        if (!strnicmp(p->f[i].name, qs, qslen)) { p->cur = i; return; }
    }
    qs[--qslen] = 0;
}

int main(int argc, char **argv) {
    int have = 0, i, c;
    char cwd[80], fn[90], nm[13];
    unsigned k;
    PANEL *p;
    FENT *e;
    Buscar_Cargador(argc, argv);
    if (!lsh)
    {
        unsigned w;
        static const char msg[] = "Use NC.COM to start NC.\r\n";
        _dos_write(1, msg, sizeof msg - 1, &w);
        return 1;
    }
    if (argv[0] && argv[0][0])
    {
        char *bs;
        strncpy(extdir, argv[0], 79);
        extdir[79] = 0;
        bs = strrchr(extdir, '\\');
        if (!bs) bs = strchr(extdir, ':');
        if (bs) bs[1] = 0; else extdir[0] = 0;
    }
    _harderr(error_Disco);
    _dos_setvect(0x23, Sin_Ctrlc);
    Ini_Video();
    Guardar_pant();
    Ini_Buffer();
    pan[0].x = 0;
    pan[1].x = 40;
    if (!getcwd(cwd, 80)) strcpy(cwd, "C:\\");
    if (lsh && lsh->have)
    {
        _fmemcpy(&st, &lsh->u.s, sizeof st);
        have = 1;
    }
    if (!have) leer_Ini();
    for (i = 0; i < 2; i++) {
        if (have) { pan[i].brief = st.brief[i]; pan[i].sort = st.sort[i]; }
        strcpy(pan[i].path, have ? st.path[i] : cwd);
        if (Leer_Dir(&pan[i])) { strcpy(pan[i].path, cwd); Leer_Dir(&pan[i]); }
        else if (have) { pan[i].top = st.top[i]; Buscar_Cursor(&pan[i], st.cur[i]); }
        Ajustar_vista(&pan[i]);
    }
    if (have) { act = st.act & 1; pan[0].brief = st.brief[0]; pan[1].brief = st.brief[1]; }
    else act = 1;
    Forma_cursor(1);
    if (lsh && lsh->err)
    {
        dib_todo();
        fmt(fn, "Cannot run (DOS error %d)", lsh->err);
        lsh->err = 0;
        Aviso("Error", fn);
    }

    for (;;)
    {
        if (!_bios_keybrd(_KEYBRD_READY))
        {
            if (needfull) dib_todo();
            else if (moved) Dib_Rapido();
            Marcar_Dibujado();
        }
        clockon = 1;
        k = Leer_Tecla();
        clockon = 0;
        if (k == K_UP || k == K_DOWN || k == K_PGUP || k == K_PGDN || k == K_HOME ||
            k == K_END || k == K_LEFT || k == K_RIGHT) moved = 1;
        else needfull = 1;
        p = &pan[act];
        e = p->n ? &p->f[p->cur] : NULL;
        c = letra_alt(k);
        if (c) {
            if (qslen < 12) { qs[qslen++] = (char)c; qs[qslen] = 0; Busqueda_rapida(p); }
            Ajustar_vista(p);
            continue;
        }
        qslen = 0; qs[0] = 0;
        switch (k)
        {
        case K_UP:   p->cur--; break;
        case K_DOWN: p->cur++; break;
        case K_PGUP: p->cur -= p->brief ? 3 * BROWS : PROWS - 1; break;
        case K_PGDN: p->cur += p->brief ? 3 * BROWS : PROWS - 1; break;
        case K_LEFT: if (p->brief && !cmdlen) p->cur -= BROWS; break;
        case K_RIGHT: if (p->brief && !cmdlen) p->cur += BROWS; break;
        case K_CF1: pan[0].brief ^= 1; Ajustar_vista(&pan[0]); Guardar_ini(); break;
        case K_CF2: pan[1].brief ^= 1; Ajustar_vista(&pan[1]); Guardar_ini(); break;
        case K_CTF3: case K_CTF4: case K_CTF5: case K_CTF6:
            p->sort = (k - K_CTF3) >> 8;
            Reordenar(p); Guardar_ini();
            break;
        case K_CTRLA: Hacer_Atrib(); break;
        case K_HOME: p->cur = 0; break;
        case K_END:  p->cur = p->n - 1; break;
        case K_TAB:  act ^= 1; break;
        case K_INS:
            if (e && strcmp(e->name, "..")) {
                e->sel ^= 1;
                p->nsel += e->sel ? 1 : -1;
            }
            p->cur++;
            break;
        case K_ENTER:
            if (cmdlen) { Ejecutar_Linea(cmd); break; }
            if (!e) break;
            if (e->attr & _A_SUBDIR)
            {
                if (!strcmp(e->name, "..")) {
                    strcpy(fn, p->path);
                    Quitar_Dir(fn, nm);
                    cambiar_panel(p, fn, nm);
                } else {
                    unir_ruta(fn, p->path, e->name);
                    cambiar_panel(p, fn, NULL);
                }
            } else if (es_exe(e->name)) {
                strcpy(nm, e->name);
                Ejecutar(nm, stricmp(strrchr(nm, '.'), ".BAT") != 0);
            } else if (Buscar_Ext(e->name, fn)) {

                quiet = extdir[0] && !strnicmp(fn, extdir, strlen(extdir));
                Ejecutar(fn, 0);
                quiet = 0;
            }
            break;
        case K_CENT:
        case K_CTRLJ:
            if (e && cmdlen + 14 < 120)
            {
                if (cmdlen && cmd[cmdlen - 1] != ' ') strcat(cmd, " ");
                strcat(cmd, e->name);
                strcat(cmd, " ");
                cmdlen = strlen(cmd);
            }
            break;
        case K_ESC: cmd[0] = 0; cmdlen = 0; break;
        case K_BS:  if (cmdlen) cmd[--cmdlen] = 0; break;
        case K_F4:
            if (e && !(e->attr & _A_SUBDIR))
            {
                unir_ruta(fn, p->path, e->name);
                editor(fn, p->path);
                refrescar(0);
                refrescar(1);
            }
            break;
        case K_F2: Menu_f2(); break;
        case K_F3:
            if (e && !(e->attr & _A_SUBDIR)) { unir_ruta(fn, p->path, e->name); visor(fn); }
            else if (e && strcmp(e->name, "..")) info_Dir(p, e);
            break;
        case K_F5:  hacer_copiar(0); break;
        case K_F6:  hacer_copiar(1); break;
        case K_F7:  Hacer_Dir(); break;
        case K_AF7: hacer_Fichero(); break;
        case K_AF6: hacer_Renombrar(); break;
        case K_CTRLF: hacer_Buscar(); break;
        case K_CTRLD: Hacer_comparar(); break;
        case K_F8:  hacer_borrar(); break;
        case K_F9:  Hacer_Menu(); break;
        case K_F10:

            Salir();
            break;
        case K_AF1: hacer_unidad(0); break;
        case K_AF2: hacer_unidad(1); break;
        case K_CTRLR: refrescar(0); refrescar(1); break;
        case K_CTRLO: Ver_Pant_dos(); Forma_cursor(1); Leer_Tecla(); break;
        case K_CTRLC: calculadora(); break;
        default:
            c = k & 0xFF;
            if (!cmdlen && c == '+') hacer_sel(1);
            else if (!cmdlen && c == '-') hacer_sel(0);
            else if (!cmdlen && c == '*') invertir_Sel(p);
            else if (c >= 32 && cmdlen < 120) { cmd[cmdlen++] = (char)c; cmd[cmdlen] = 0; }
            break;
        }
        if (k == K_UP || k == K_DOWN || k == K_PGUP || k == K_PGDN) vaciar_teclas();
        Ajustar_vista(&pan[act]);
    }
    return 0;
}
