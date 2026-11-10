
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdarg.h>
#include <dos.h>
#include <i86.h>
#include <bios.h>
#include <io.h>
#include <conio.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>

#define NC_     26
#define NR_     99
#define VROWS   21
#define LIM     2000000000L
#define ELEN    70

#define K_UP    0x4800
#define K_DOWN  0x5000
#define K_LEFT  0x4B00
#define K_RIGHT 0x4D00
#define K_PGUP  0x4900
#define K_PGDN  0x5100
#define K_HOME  0x4700
#define K_END   0x4F00
#define K_DEL   0x5300
#define K_F1    0x3B00
#define K_F2    0x3C00
#define K_F3    0x3D00
#define K_F4    0x3E00
#define K_F5    0x3F00
#define K_F6    0x4000
#define K_F7    0x4100
#define K_F8    0x4200
#define K_F9    0x4300
#define K_F10   0x4400
#define K_CHOME 0x7700
#define K_AA    0x1E00
#define K_AZ    0x2C00
#define K_AS    0x1F00
#define K_AX    0x2D00
#define K_AM    0x3200
#define K_AD    0x2000
#define K_AP    0x1900
#define K_CTRLS 0x1F13
#define K_CTRLP 0x1910
#define K_STAB  0x0F00
#define K_TAB   0x0F09
#define K_ENTER 0x1C0D
#define K_ESC   0x011B

enum { E_OK, E_DIV, E_REF, E_SINT, E_CIC, E_OVF };
static const char *errn[] = { "", "#DIV/0", "#REF", "#SYNT", "#LOOP", "#OVFL" };

typedef struct {
    char *s;
    long v;
    unsigned char st, e, k;
} CELL;

static CELL sh[NR_][NC_];
static int cw[NC_];
static char au[NC_];
static int needfit;
static int cc, cr, tr, lc;
static int decm = 3;
static int modif;
static char fname[80];
static char msg[64];
static char clip[ELEN + 6];
static int clipc, clipr, hasclip;

enum { H_CELL, H_CUR, H_HDR, H_HDRC, H_BAR, H_KEYN, H_KEYL, H_DLG, H_INP, H_BTN, H_BTNF,
       H_ERR, H_ERSH, H_ERRV, H_EDIT, H_STAT, H_LINE, H_SELD, H_LCD, H_LCDD, H_LCDB };
static unsigned char colc[] = { 0x1F,0x30,0x70,0x8F,0x30,0x07,0x30,0x30,0x0F,0x70,0x2F,0x4F,0x40,0x1C,0x0F,0x2F,0x19,0x0F,0x0A,0x02,0x08 };
static unsigned char colm[] = { 0x07,0x70,0x07,0x0F,0x70,0x07,0x70,0x70,0x07,0x07,0x0F,0x70,0x70,0x0F,0x07,0x70,0x07,0x0F,0x0F,0x07,0x07 };
static unsigned char *col;
static unsigned short __far *vid;
static unsigned short __far *vreal;
static unsigned short vbuf[2000];
static unsigned short vsave[2000];
static int mono, vdirty, sx, sy;

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
        switch (*f++)
        {
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

static void blink(int on) {
    union REGS r;
    r.x.ax = 0x1003; r.h.bl = (unsigned char)on; r.h.bh = 0;
    int86(0x10, &r, &r);
}

static void Ini_Video(void)
{
    union REGS r;
    r.h.ah = 0x0F;
    int86(0x10, &r, &r);
    if (r.h.al == 7) {
        mono = 1;
        vreal = (unsigned short __far *)MK_FP(0xB000, 0);
    } else {
        mono = 0;
        vreal = (unsigned short __far *)MK_FP(0xB800, 0);
        if (r.h.al != 2 && r.h.al != 3) {
            r.x.ax = 3;
            int86(0x10, &r, &r);
        }
    }
    r.h.ah = 3; r.h.bh = 0;
    int86(0x10, &r, &r);
    sx = r.h.dl; sy = r.h.dh;
    _fmemcpy((void __far *)vsave, vreal, 4000);
    _fmemcpy((void __far *)vbuf, vreal, 4000);
    vid = (unsigned short __far *)vbuf;
    col = mono ? colm : colc;
    if (!mono) blink(0);
}

static void Volcar(void)
{
    if (!vdirty) return;
    vdirty = 0;
    if (!mono)
    {
        while (inp(0x3DA) & 8) ;
        while (!(inp(0x3DA) & 8)) ;
    }
    _fmemcpy(vreal, (void __far *)vbuf, 4000);
}

static void Fin_Video(void) {
    _fmemcpy(vreal, (void __far *)vsave, 4000);
    if (!mono) blink(1);
    Forma_cursor(1);
    pos_cursor(sx, sy);
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

static void poner_Txt(int x, int y, int a, const char *s, int w)
{
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
    if (title && *title)
    {
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

static void Boton(int x, int y, const char *s, int focus, int sh_) {
    int l = strlen(s);
    poner_Txt(x, y, focus ? H_BTNF : H_BTN, s, l);
    poner_car(x + l, y, sh_, 0xDC);
    linea_H(x + 1, y + 1, l, sh_, 0xDF);
}
#define button(x, y, s, f) Boton(x, y, s, f, H_DLG)

static unsigned Norm_Tecla(unsigned k) {
    if ((k & 0xFF) == 0xE0 && (k >> 8)) k &= 0xFF00;
    else if ((k & 0xFF) == 0) k &= 0xFF00;
    if ((k >> 8) == 0xE0) k = 0x1C00 | (k & 0xFF);
    return k;
}

static unsigned Leer_Tecla(void)
{
    if (!_bios_keybrd(_KEYBRD_READY)) Volcar();
    while (!_bios_keybrd(_KEYBRD_READY)) ;
    return Norm_Tecla(_bios_keybrd(_KEYBRD_READ));
}

static int pedir_tecla(const char *title, const char *l1)
{
    int f = 0, c;
    unsigned k;
    Forma_cursor(0);
    for (;;)
    {
        Caja(10, 9, 60, 6, H_DLG, title);
        poner_Txt(12, 10, H_DLG, l1, 56);
        button(21, 12, "  Yes   ", f == 0);
        button(33, 12, "   No   ", f == 1);
        button(45, 12, " Cancel ", f == 2);
        k = Leer_Tecla();
        c = k & 0xFF;
        if (c == 27) { c = 27; break; }
        if (c == 13) { c = f == 0 ? 'Y' : f == 1 ? 'N' : 27; break; }
        if (k == K_LEFT) f = (f + 2) % 3;
        else if (k == K_RIGHT || c == 9) f = (f + 1) % 3;
        else
        {
            c = toupper(c);
            if (c == 'Y' || c == 'N') break;
        }
    }
    return c;
}

static void Aviso(const char *title, const char *text) {
    Caja(10, 9, 60, 6, H_ERR, title);
    poner_Txt(12, 10, H_ERR, text, 56);
    Boton(37, 12, "  Ok  ", 1, H_ERSH);
    Leer_Tecla();
}

static int pedir_Texto(const char *title, const char *prompt, char *buf, int max) {
    int l = strlen(buf), cp = l, off, c;
    unsigned k;
    for (;;) {
        Caja(10, 9, 60, 7, H_DLG, title);
        poner_Txt(12, 10, H_DLG, prompt, 56);
        off = cp > 53 ? cp - 53 : 0;
        poner_car(12, 11, H_DLG, '[');
        poner_Txt(13, 11, H_INP, buf + off, 54);
        poner_car(67, 11, H_DLG, ']');
        button(23, 13, "  Ok  ", 1);
        button(39, 13, " Cancel ", 0);
        Forma_cursor(1);
        pos_cursor(13 + cp - off, 11);
        k = Leer_Tecla();
        c = k & 0xFF;
        if (k == K_LEFT) { if (cp) cp--; }
        else if (k == K_RIGHT) { if (cp < l) cp++; }
        else if (k == K_HOME) cp = 0;
        else if (k == K_END) cp = l;
        else if (k == K_DEL) {
            if (cp < l) { memmove(buf + cp, buf + cp + 1, l - cp); l--; }
        }
        else if (c == 13) { Forma_cursor(0); return 1; }
        else if (c == 27) { Forma_cursor(0); return 0; }
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

static void Repro_cd(void);

static void Caja_Ayuda(void)
{
    static const char *t[] = {
        "Arrows, PgUp/PgDn, Home, Ctrl+Home : move",
        "Type              : edit the cell (Enter/arrows accept)",
        "F2                : edit the cell contents",
        "Del or F8         : delete cell",
        "F5 / F6           : copy / paste (adjusts references)",
        "F7                : go to a cell (e.g. C12)",
        "F3 / F4 / Ctrl+S  : open / save as / save",
        "Ctrl+P            : CD player",
        "F9                : decimals (auto,0,1,2)",
        "Alt+A / Alt+Z     : column width by hand (default: auto)",
        "Alt+S / Alt+M / Alt+D : sum / multiply / divide cells above",
        "Alt+P             : percentage of a cell",
        "F10 or Esc        : exit",
        "",
        "Formulas: =A1+B2*3  =(A1+A2)/2  =50%  =SUM(A1:A9)",
        "          SUM AVG MIN MAX COUNT MUL DIV  (range A1:B5 or list A1;B2)",
        "Text: just type. A ' in front forces text."
    };
    int i;
    Caja(7, 1, 66, 23, H_DLG, "Help");
    for (i = 0; i < 17; i++) poner_Txt(9, 3 + i, H_DLG, t[i], 62);
    Leer_Tecla();
}

static int perr, depth;
static const char *ip;

static void saltar_Esp(void) { while (*ip == ' ') ip++; }

static long evaluar_Celda(int c, int r);
static long Expresion(void);

static long Token_Num(int comma) {
    long v = 0, f = 0;
    int n = 0;
    while (isdigit((unsigned char)*ip))
    {
        v = v * 10 + (*ip++ - '0');
        if (v > 20000000L) { perr = E_OVF; v = 0; }
    }
    v *= 100;
    if (*ip == '.' || (comma && *ip == ',')) {
        ip++;
        while (isdigit((unsigned char)*ip)) {
            if (n < 2) { f = f * 10 + (*ip - '0'); n++; }
            ip++;
        }
    }
    while (n < 2) { f *= 10; n++; }
    return v + f;
}

static int Leer_Ref(int *c, int *r)
{
    const char *q = ip;
    int rr = 0;
    if (!isalpha((unsigned char)*q)) return 0;
    *c = toupper((unsigned char)*q) - 'A';
    q++;
    if (!isdigit((unsigned char)*q)) return 0;
    while (isdigit((unsigned char)*q)) { if (rr < 1000) rr = rr * 10 + (*q - '0'); q++; }
    if (isalpha((unsigned char)*q)) return 0;
    ip = q;
    if (rr < 1 || rr > NR_) { perr = E_REF; rr = 1; }
    *r = rr - 1;
    return 1;
}

static long Sumar(long a, long b)
{
    if (b > 0 ? a > LIM - b : a < -LIM - b) { perr = E_OVF; return 0; }
    return a + b;
}

static long multiplicar(long a, long b) {
    unsigned long ua, ub, ah, al, bh, bl, r;
    int neg = 0;
    if (a < 0) { ua = -a; neg ^= 1; } else ua = a;
    if (b < 0) { ub = -b; neg ^= 1; } else ub = b;
    ah = ua / 100; al = ua % 100; bh = ub / 100; bl = ub % 100;
    if (ah && bh > (unsigned long)(LIM / 100) / ah) { perr = E_OVF; return 0; }
    r = ah * bh * 100 + ah * bl + al * bh + al * bl / 100;
    if (r > (unsigned long)LIM) { perr = E_OVF; return 0; }
    return neg ? -(long)r : (long)r;
}

static long dividir(long a, long b)
{
    unsigned long ua, ub, q, rem, fr;
    int neg = 0;
    if (b == 0) { perr = E_DIV; return 0; }
    if (a < 0) { ua = -a; neg ^= 1; } else ua = a;
    if (b < 0) { ub = -b; neg ^= 1; } else ub = b;
    q = ua / ub; rem = ua % ub;
    if (q > (unsigned long)(LIM / 100)) { perr = E_OVF; return 0; }
    if (ub >= 40000000UL) { rem /= 100; ub /= 100; }
    fr = rem * 100 / ub;
    q = q * 100 + fr;
    if (q > (unsigned long)LIM) { perr = E_OVF; return 0; }
    return neg ? -(long)q : (long)q;
}

typedef struct { long sum, mn, mx; int n, mode; } ACC;

static void acumular(ACC *a, long v)
{
    if (a->mode)
    {
        if (a->n == 0) a->sum = v;
        else if (a->mode == 1) a->sum = multiplicar(a->sum, v);
        else if (v != 0) a->sum = dividir(a->sum, v);
        a->n++;
        return;
    }
    if (a->n == 0 || v < a->mn) a->mn = v;
    if (a->n == 0 || v > a->mx) a->mx = v;
    a->sum = Sumar(a->sum, v);
    a->n++;
}

static long funcion(const char *w) {
    ACC a;
    int c1, r1, c2, r2, c, r, t;
    const char *sv;
    long v;
    a.sum = 0; a.mn = 0; a.mx = 0; a.n = 0;
    a.mode = !strcmp(w, "MUL") ? 1 : !strcmp(w, "DIV") ? 2 : 0;
    ip++;
    for (;;) {
        saltar_Esp();
        if (*ip == ')') { ip++; break; }
        sv = ip;
        if (Leer_Ref(&c1, &r1) && *ip == ':') {
            ip++;
            if (!Leer_Ref(&c2, &r2)) perr = E_SINT;
            if (perr) break;
            if (c1 > c2) { t = c1; c1 = c2; c2 = t; }
            if (r1 > r2) { t = r1; r1 = r2; r2 = t; }
            for (r = r1; r <= r2 && !perr; r++)
                for (c = c1; c <= c2 && !perr; c++) {
                    v = evaluar_Celda(c, r);
                    if (!perr && (sh[r][c].k == 1 || sh[r][c].k == 3)) acumular(&a, v);
                }
        } else {
            ip = sv;
            v = Expresion();
            if (!perr) acumular(&a, v);
        }
        if (perr) break;
        saltar_Esp();
        if (*ip == ';' || *ip == ',') { ip++; continue; }
        if (*ip == ')') { ip++; break; }
        perr = E_SINT;
        break;
    }
    if (perr) return 0;
    if (!strcmp(w, "SUM") || !strcmp(w, "SUMA")) return a.sum;
    if (!strcmp(w, "AVG") || !strcmp(w, "PROM")) return a.n ? a.sum / a.n : 0;
    if (a.mode) return a.sum;
    if (!strcmp(w, "MIN")) return a.mn;
    if (!strcmp(w, "MAX")) return a.mx;
    if (!strcmp(w, "COUNT") || !strcmp(w, "CONT")) return (long)a.n * 100;
    perr = E_SINT;
    return 0;
}

static long Valor_simple(void) {
    long v = 0;
    int c, r, n;
    char w[10];
    saltar_Esp();
    if (*ip == '(') {
        ip++;
        v = Expresion();
        saltar_Esp();
        if (*ip == ')') ip++; else perr = E_SINT;
    } else if (isdigit((unsigned char)*ip) || *ip == '.') {
        v = Token_Num(0);
    } else if (isalpha((unsigned char)*ip)) {
        if (Leer_Ref(&c, &r))
        {
            if (!perr) v = evaluar_Celda(c, r);
        } else {
            n = 0;
            while (isalpha((unsigned char)*ip))
            {
                if (n < 8) w[n++] = (char)toupper((unsigned char)*ip);
                ip++;
            }
            w[n] = 0;
            saltar_Esp();
            if (*ip == '(') v = funcion(w); else perr = E_SINT;
        }
    } else {
        perr = E_SINT;
    }
    saltar_Esp();
    while (*ip == '%' && !perr) { ip++; v /= 100; saltar_Esp(); }
    return v;
}

static long Unico_valor(void)
{
    saltar_Esp();
    if (*ip == '-') { ip++; return -Unico_valor(); }
    if (*ip == '+') { ip++; return Unico_valor(); }
    return Valor_simple();
}

static long termino(void)
{
    long a = Unico_valor(), b;
    for (;;)
    {
        saltar_Esp();
        if (perr) return 0;
        if (*ip == '*') { ip++; b = Unico_valor(); a = multiplicar(a, b); }
        else if (*ip == '/') { ip++; b = Unico_valor(); a = dividir(a, b); }
        else break;
    }
    return a;
}

static long Expresion(void) {
    long a = termino(), b;
    for (;;)
    {
        saltar_Esp();
        if (perr) return 0;
        if (*ip == '+') { ip++; b = termino(); a = Sumar(a, b); }
        else if (*ip == '-') { ip++; b = termino(); a = Sumar(a, -b); }
        else break;
    }
    return a;
}

static long evaluar_Celda(int c, int r) {
    CELL *p = &sh[r][c];
    const char *sv, *s;
    int sperr;
    long v;
    if (p->st == 1 || depth > 40) { perr = E_CIC; return 0; }
    if (p->st == 0) {
        sv = ip; sperr = perr;
        p->st = 1; perr = 0; depth++;
        s = p->s;
        v = 0;
        if (!s) p->k = 0;
        else if (*s == '=') {
            p->k = 3;
            ip = s + 1;
            v = Expresion();
            saltar_Esp();
            if (!perr && *ip) perr = E_SINT;
        } else if (*s == '\'') p->k = 2;
        else {
            int neg = 0;
            ip = s;
            saltar_Esp();
            if (*ip == '-') { neg = 1; ip++; } else if (*ip == '+') ip++;
            if (isdigit((unsigned char)*ip) || *ip == '.' || *ip == ',') {
                v = Token_Num(1);
                if (neg) v = -v;
                saltar_Esp();
                if (*ip == '%') { ip++; v /= 100; saltar_Esp(); }
                p->k = (*ip == 0 && !perr) ? 1 : 2;
                if (p->k == 2) { v = 0; perr = 0; }
            } else p->k = 2;
        }
        p->v = perr ? 0 : v;
        p->e = (unsigned char)perr;
        p->st = 2;
        depth--;
        ip = sv; perr = sperr;
    }
    if (p->e) perr = p->e;
    return p->v;
}

static void Invalidar(void) {
    int r, c;
    for (r = 0; r < NR_; r++)
        for (c = 0; c < NC_; c++) sh[r][c].st = 0;
    needfit = 1;
}

static void poner_texto(int c, int r, const char *s) {
    CELL *p = &sh[r][c];
    if (p->s) { free(p->s); p->s = 0; }
    if (s && *s) {
        p->s = (char *)malloc(strlen(s) + 1);
        if (!p->s) fmt(msg, "Out of memory");
        else strcpy(p->s, s);
    }
}

static void Poner_celda(int c, int r, const char *s) {
    poner_texto(c, r, s);
    modif = 1;
    Invalidar();
}

static void borrar_todo(void)
{
    int r, c;
    for (r = 0; r < NR_; r++)
        for (c = 0; c < NC_; c++) {
            if (sh[r][c].s) free(sh[r][c].s);
            sh[r][c].s = 0;
            sh[r][c].st = 0;
        }
    for (c = 0; c < NC_; c++) { cw[c] = 10; au[c] = 1; }
    decm = 3;
    needfit = 1;
}

static void fmt_numero(char *o, long v)
{
    unsigned long u, i, f;
    int neg = v < 0, dm = decm;
    u = neg ? (unsigned long)(-v) : (unsigned long)v;
    if (dm == 0) u = (u + 50) / 100 * 100;
    else if (dm == 1) u = (u + 5) / 10 * 10;
    i = u / 100; f = u % 100;
    if (dm == 3) dm = f == 0 ? 0 : (f % 10 == 0 ? 1 : 2);
    o += fmt(o, "%s%lu", (neg && u) ? "-" : "", i);
    if (dm == 1) fmt(o, ".%d", (int)(f / 10));
    else if (dm == 2) fmt(o, ".%02d", (int)f);
}

static void Mover_refs(const char *s, char *d, int dc, int dr)
{
    const char *q;
    int c, r, prev = 0;
    while (*s)
    {
        if (isalpha((unsigned char)*s) && !isalnum(prev)) {
            q = s;
            c = toupper((unsigned char)*q) - 'A'; q++;
            if (isdigit((unsigned char)*q))
            {
                r = 0;
                while (isdigit((unsigned char)*q)) { if (r < 1000) r = r * 10 + (*q - '0'); q++; }
                if (!isalpha((unsigned char)*q)) {
                    c += dc; r += dr;
                    if (c < 0 || c >= NC_ || r < 1 || r > NR_) { *d++ = 'A'; *d++ = '0'; }
                    else d += fmt(d, "%c%d", 'A' + c, r);
                    prev = '0';
                    s = q;
                    continue;
                }
            }
        }
        prev = *s;
        *d++ = *s++;
    }
    *d = 0;
}

static char rb[512], wb[1024];
static int rpos, rlen, wlen;

static int leer_linea(int fd, char *ln, int max)
{
    int n = 0, c;
    for (;;) {
        if (rpos >= rlen) {
            rlen = read(fd, rb, 512);
            rpos = 0;
            if (rlen <= 0) { rlen = 0; if (n == 0) return 0; break; }
        }
        c = rb[rpos++];
        if (c == '\n') break;
        if (c == '\r' || c == 26) continue;
        if (n < max - 1) ln[n++] = (char)c;
    }
    ln[n] = 0;
    return 1;
}

static int vaciar_esc(int fd)
{
    int ok = 1;
    if (wlen && write(fd, wb, wlen) != wlen) ok = 0;
    wlen = 0;
    return ok;
}

static int escribir_linea(int fd, const char *s) {
    int l = strlen(s);
    if (wlen + l + 2 > 1024) if (!vaciar_esc(fd)) return 0;
    memcpy(wb + wlen, s, l);
    wlen += l;
    wb[wlen++] = '\r';
    wb[wlen++] = '\n';
    return 1;
}

static int guardar_fich(const char *name) {
    int fd, r, c, ok = 1;
    char ln[100], t[12];
    fd = open(name, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, S_IREAD | S_IWRITE);
    if (fd < 0) return 0;
    wlen = 0;
    ok = escribir_linea(fd, "HOJA 1");
    fmt(ln, "D %d", decm);
    ok = ok && escribir_linea(fd, ln);
    strcpy(ln, "W");
    for (c = 0; c < NC_; c++) { fmt(t, " %d", au[c] ? 0 : cw[c]); strcat(ln, t); }
    ok = ok && escribir_linea(fd, ln);
    for (r = 0; r < NR_ && ok; r++)
        for (c = 0; c < NC_ && ok; c++)
            if (sh[r][c].s) {
                fmt(ln, "%c%d %.78s", 'A' + c, r + 1, sh[r][c].s);
                ok = escribir_linea(fd, ln);
            }
    ok = ok && vaciar_esc(fd);
    close(fd);
    return ok;
}

static int Cargar_Fich(const char *name) {
    int fd, c, r, n;
    char ln[100];
    const char *q;
    fd = open(name, O_RDONLY | O_BINARY);
    if (fd < 0) return 0;
    rpos = rlen = 0;
    borrar_todo();
    while (leer_linea(fd, ln, 100)) {
        if (!ln[0] || !strncmp(ln, "HOJA", 4)) continue;
        if (ln[0] == 'D' && ln[1] == ' ') { decm = atoi(ln + 2); if (decm < 0 || decm > 3) decm = 3; continue; }
        if (ln[0] == 'W' && ln[1] == ' ') {
            q = ln + 1;
            for (c = 0; c < NC_; c++) {
                while (*q == ' ') q++;
                n = atoi(q);
                if (n >= 4 && n <= 30) { cw[c] = n; au[c] = 0; }
                while (isdigit((unsigned char)*q)) q++;
            }
            continue;
        }
        ip = ln; perr = 0;
        if (Leer_Ref(&c, &r) && !perr && *ip == ' ') poner_texto(c, r, ip + 1);
        perr = 0;
    }
    close(fd);
    modif = 0;
    Invalidar();
    return 1;
}

static int Ultima_Vis(int l) {
    int x = 3, c = l;
    while (c < NC_ && x + cw[c] <= 80) { x += cw[c]; c++; }
    return c > l ? c - 1 : l;
}

static void Asegurar_vista(void) {
    if (cr < tr) tr = cr;
    if (cr >= tr + VROWS) tr = cr - VROWS + 1;
    if (cc < lc) lc = cc;
    while (cc > Ultima_Vis(lc)) lc++;
}

static void nombre_ref(char *o, int c, int r)
{
    fmt(o, "%c%d", 'A' + c, r + 1);
}

static void dib_celda(int x, int y, int w, int c, int r, int cur) {
    CELL *p = &sh[r][c];
    char t[48], o[48];
    int a = cur ? H_CUR : H_CELL, l, i;
    perr = 0;
    evaluar_Celda(c, r);
    perr = 0;
    if (p->k == 2) {
        poner_Txt(x, y, a, (p->s[0] == '\'') ? p->s + 1 : p->s, w);
        return;
    }
    if (p->k == 0) { poner_Txt(x, y, a, "", w); return; }
    if (p->e)
    {
        strcpy(t, errn[p->e]);
        if (!cur) a = H_ERRV;
    } else fmt_numero(t, p->v);
    l = strlen(t);
    if (l > w) { for (i = 0; i < w; i++) o[i] = '#'; o[w] = 0; }
    else { memset(o, ' ', w - l); strcpy(o + w - l, t); }
    poner_Txt(x, y, a, o, w);
}

static void Dib_Teclas(void)
{
    static const char *lab[10] = { "Help","Edit","Open","Save","Copy","Paste","Go to","Delete","Decim.","Quit" };
    int i;
    char n[4];
    for (i = 0; i < 10; i++) {
        fmt(n, "%2d", i + 1);
        poner_Txt(i * 8, 24, H_KEYN, n, 2);
        poner_Txt(i * 8 + 2, 24, H_KEYL, lab[i], 6);
    }
}

static void Ajustar_Anchos(void)
{
    int c, r, l, m;
    char t[48];
    CELL *p;
    needfit = 0;
    for (c = 0; c < NC_; c++) {
        if (!au[c]) continue;
        m = 0;
        for (r = 0; r < NR_; r++) {
            p = &sh[r][c];
            if (!p->s) continue;
            perr = 0; evaluar_Celda(c, r); perr = 0;
            if (p->k == 2) l = strlen(p->s) - (p->s[0] == '\'');
            else if (p->e) l = strlen(errn[p->e]);
            else { fmt_numero(t, p->v); l = strlen(t); }
            if (l > m) m = l;
        }
        m++;
        cw[c] = m < 8 ? 8 : (m > 30 ? 30 : m);
    }
}

static void dibujar(void)
{
    int y, x, c, l, last, w;
    char t[100], o[48];
    CELL *p;

    if (needfit) Ajustar_Anchos();
    Asegurar_vista();
    last = Ultima_Vis(lc);

    nombre_ref(t, cc, cr);
    fmt(o, " %-5s", t);
    poner_Txt(0, 0, H_BAR, o, 7);
    p = &sh[cr][cc];
    poner_Txt(7, 0, H_CELL, p->s ? p->s : "", 73);

    poner_Txt(0, 1, H_HDR, "", 3);
    x = 3;
    for (c = lc; c <= last; c++) {
        w = cw[c];
        memset(o, ' ', w); o[w] = 0;
        o[w / 2] = (char)('A' + c);
        poner_Txt(x, 1, c == cc ? H_HDRC : H_HDR, o, w);
        x += w;
    }
    if (x < 80) linea_H(x, 1, 80 - x, H_HDR, ' ');

    for (y = 0; y < VROWS; y++) {
        int r = tr + y;
        if (r >= NR_) { linea_H(0, 2 + y, 80, H_CELL, ' '); continue; }
        fmt(t, "%3d", r + 1);
        poner_Txt(0, 2 + y, r == cr ? H_HDRC : H_HDR, t, 3);
        x = 3;
        for (c = lc; c <= last; c++) {
            dib_celda(x, 2 + y, cw[c] - 1, c, r, c == cc && r == cr);
            poner_car(x + cw[c] - 1, 2 + y, H_LINE, 0xB3);
            x += cw[c];
        }
        if (x < 80) linea_H(x, 2 + y, 80 - x, H_CELL, ' ');
    }

    p = &sh[cr][cc];
    perr = 0;
    evaluar_Celda(cc, cr);
    perr = 0;
    l = fmt(t, " %s%s", fname[0] ? fname : "(no name)", modif ? " *" : "");
    linea_H(0, 23, 80, H_STAT, ' ');
    poner_Txt(0, 23, H_STAT, t, 30);
    if (msg[0]) poner_Txt(30, 23, H_STAT, msg, 50);
    else if (p->k == 3 || p->k == 1) {
        if (p->e) fmt(t, "= %s", errn[p->e]);
        else { strcpy(t, "= "); fmt_numero(t + 2, p->v); }
        poner_Txt(30, 23, H_STAT, t, 50);
    }
    Dib_Teclas();
}

static char eb[ELEN + 2];

static unsigned editar_celda(int first) {
    int l, cp, off, c, typing = first != 0;
    unsigned k;
    char t[12];
    if (first) { eb[0] = (char)first; eb[1] = 0; }
    else { strcpy(eb, sh[cr][cc].s ? sh[cr][cc].s : ""); }
    l = strlen(eb); cp = l;
    Forma_cursor(1);
    for (;;) {
        dibujar();
        nombre_ref(t, cc, cr);
        poner_Txt(0, 0, H_BAR, " ", 7);
        poner_Txt(1, 0, H_BAR, t, 6);
        off = cp > 71 ? cp - 71 : 0;
        poner_Txt(7, 0, H_EDIT, eb + off, 73);
        pos_cursor(7 + cp - off, 0);
        k = Leer_Tecla();
        c = k & 0xFF;
        if (k == K_ENTER || k == K_UP || k == K_DOWN || k == K_TAB || k == K_STAB ||
            (typing && (k == K_LEFT || k == K_RIGHT))) {
            Forma_cursor(0);
            return k;
        }
        if (c == 27) { Forma_cursor(0); return 0; }
        if (k == K_LEFT) { if (cp) cp--; }
        else if (k == K_RIGHT) { if (cp < l) cp++; }
        else if (k == K_HOME) cp = 0;
        else if (k == K_END) cp = l;
        else if (k == K_DEL) {
            if (cp < l) { memmove(eb + cp, eb + cp + 1, l - cp); l--; }
        }
        else if (c == 8) {
            if (cp) { memmove(eb + cp - 1, eb + cp, l - cp + 1); cp--; l--; }
        }
        else if (c >= 32 && l < ELEN) {
            memmove(eb + cp + 1, eb + cp, l - cp + 1);
            eb[cp++] = (char)c;
            l++;
        }
    }
}

static void mover(unsigned k)
{
    if (k == K_ENTER || k == K_DOWN) { if (cr < NR_ - 1) cr++; }
    else if (k == K_UP) { if (cr) cr--; }
    else if (k == K_RIGHT || k == K_TAB) { if (cc < NC_ - 1) cc++; }
    else if (k == K_LEFT || k == K_STAB) { if (cc) cc--; }
}

static int celda_Num(int c, int r)
{
    perr = 0;
    evaluar_Celda(c, r);
    perr = 0;
    return sh[r][c].k == 1 || sh[r][c].k == 3;
}

static void sumar_auto(const char *fn) {
    int r, c, top = -1;
    char t[40], a[8], b[8];
    for (r = 0; r < cr; r++) if (celda_Num(cc, r)) { top = r; break; }
    if (top >= 0) {
        nombre_ref(a, cc, top); nombre_ref(b, cc, cr - 1);
    } else {
        for (c = 0; c < cc; c++) if (celda_Num(c, cr)) { top = c; break; }
        if (top < 0) { fmt(msg, "Nothing to calculate"); return; }
        nombre_ref(a, top, cr); nombre_ref(b, cc - 1, cr);
    }
    fmt(t, "=%s(%s:%s)", fn, a, b);
    Poner_celda(cc, cr, t);
}

static void Hacer_Porcentaje(void)
{
    char o[12], p[12], t[30];
    o[0] = 0; p[0] = 0;
    if (!pedir_Texto("Percentage", "Source cell (e.g. B3):", o, 8) || !o[0]) return;
    if (!pedir_Texto("Percentage", "Percentage (e.g. 20):", p, 8) || !p[0]) return;
    fmt(t, "=%s*%s%%", o, p);
    Poner_celda(cc, cr, t);
}

static char csvsep = ';';

static int es_Csv(const char *n) {
    int l = strlen(n);
    return l > 4 && n[l - 4] == '.' && toupper((unsigned char)n[l - 3]) == 'C' &&
           toupper((unsigned char)n[l - 2]) == 'S' && toupper((unsigned char)n[l - 1]) == 'V';
}

static void poner_campo(int c, int r, char *f, int n)
{
    char t[ELEN + 4];
    while (n > 0 && f[n - 1] == ' ') n--;
    f[n] = 0;
    if (!n) return;
    if (f[0] == '=') { t[0] = '\''; strcpy(t + 1, f); poner_texto(c, r, t); }
    else poner_texto(c, r, f);
}

static int Cargar_Csv(const char *name, const char *spec)
{
    int fd, r = 0, c, n, q, nw = 0, w[NC_], fixed, len, k;
    char ln[200], f[ELEN + 2];
    const char *s, *p;
    fixed = isdigit((unsigned char)spec[0]);
    if (fixed)
    {
        p = spec;
        while (*p && nw < NC_)
        {
            w[nw++] = atoi(p);
            while (isdigit((unsigned char)*p)) p++;
            while (*p && !isdigit((unsigned char)*p)) p++;
        }
    } else if (!spec[0]) csvsep = ';';
    else if (toupper((unsigned char)spec[0]) == 'T' && spec[1]) csvsep = '\t';
    else csvsep = spec[0];
    fd = open(name, O_RDONLY | O_BINARY);
    if (fd < 0) return 0;
    rpos = rlen = 0;
    borrar_todo();
    while (r < NR_ && leer_linea(fd, ln, 200)) {
        s = ln;
        if (fixed)
        {
            len = strlen(ln);
            k = 0;
            for (c = 0; c < nw && c < NC_ && k < len; c++) {
                n = 0;
                while (k < len && n < w[c]) { if (n < ELEN) f[n] = ln[k]; n++; k++; }
                if (n > ELEN) n = ELEN;
                q = 0;
                while (q < n && f[q] == ' ') q++;
                memmove(f, f + q, n - q);
                poner_campo(c, r, f, n - q);
            }
        } else {
            c = 0;
            while (c < NC_) {
                n = 0; q = 0;
                if (*s == '"') { q = 1; s++; }
                while (*s) {
                    if (q) {
                        if (*s == '"') {
                            if (s[1] == '"') { if (n < ELEN) f[n++] = '"'; s += 2; continue; }
                            s++; q = 0; continue;
                        }
                        if (n < ELEN) f[n++] = *s;
                        s++;
                    } else {
                        if (*s == csvsep) break;
                        if (n < ELEN) f[n++] = *s;
                        s++;
                    }
                }
                poner_campo(c, r, f, n);
                c++;
                if (*s == csvsep) s++; else break;
            }
        }
        r++;
    }
    close(fd);
    modif = 0;
    Invalidar();
    return 1;
}

static int Escribir_crudo(int fd, const char *s)
{
    int l = strlen(s);
    if (wlen + l > 1000) if (!vaciar_esc(fd)) return 0;
    memcpy(wb + wlen, s, l);
    wlen += l;
    return 1;
}

static int guardar_csv(const char *name)
{
    int fd, r, c, maxr = -1, maxc = -1, ok = 1, sd = decm;
    char t[48], sp[2];
    const char *s;
    for (r = 0; r < NR_; r++)
        for (c = 0; c < NC_; c++)
            if (sh[r][c].s) { if (r > maxr) maxr = r; if (c > maxc) maxc = c; }
    fd = open(name, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, S_IREAD | S_IWRITE);
    if (fd < 0) return 0;
    wlen = 0;
    sp[0] = csvsep; sp[1] = 0;
    decm = 3;
    for (r = 0; r <= maxr && ok; r++) {
        for (c = 0; c <= maxc && ok; c++) {
            perr = 0; evaluar_Celda(c, r); perr = 0;
            if (c) ok = Escribir_crudo(fd, sp);
            if (sh[r][c].k == 2) {
                s = sh[r][c].s[0] == '\'' ? sh[r][c].s + 1 : sh[r][c].s;
                if (strchr(s, csvsep) || strchr(s, '"'))
                {
                    char *d = t;
                    ok = ok && Escribir_crudo(fd, "\"");
                    while (*s && ok) {
                        d = t;
                        while (*s && d < t + 40) { if (*s == '"') *d++ = '"'; *d++ = *s++; }
                        *d = 0;
                        ok = Escribir_crudo(fd, t);
                    }
                    ok = ok && Escribir_crudo(fd, "\"");
                } else ok = ok && Escribir_crudo(fd, s);
            } else if (sh[r][c].k) {
                if (sh[r][c].e) strcpy(t, errn[sh[r][c].e]);
                else {
                    char *d;
                    fmt_numero(t, sh[r][c].v);
                    if (csvsep == ';') for (d = t; *d; d++) if (*d == '.') *d = ',';
                }
                ok = ok && Escribir_crudo(fd, t);
            }
        }
        ok = ok && Escribir_crudo(fd, "\r\n");
    }
    decm = sd;
    ok = ok && vaciar_esc(fd);
    close(fd);
    return ok;
}

static int abrir_Fich(const char *name) {
    char spec[40];
    int fd;
    if (!es_Csv(name)) return Cargar_Fich(name);
    fd = open(name, O_RDONLY | O_BINARY);
    if (fd < 0) return 0;
    close(fd);
    strcpy(spec, ";");
    if (!pedir_Texto("Open CSV", "Separator (; , tab) or fixed widths (e.g. 10,5,8):", spec, 38)) return -1;
    return Cargar_Csv(name, spec);
}

static void Hacer_Guardar(int ask) {
    char n[80];
    if (ask || !fname[0])
    {
        strcpy(n, fname[0] ? fname : "SHEET1.HOJ");
        if (!pedir_Texto("Save", "File name:", n, 70)) return;
        if (!n[0]) return;
        strcpy(fname, n);
    }
    if (es_Csv(fname) ? guardar_csv(fname) : guardar_fich(fname)) { modif = 0; fmt(msg, "Saved"); }
    else Aviso("Error", "Cannot save file");
}

static int hacer_Salir(void)
{
    int a;
    if (!modif) return 1;
    a = pedir_tecla("Quit", "Save changes before quitting?");
    if (a == 27) return 0;
    if (a == 'Y') { Hacer_Guardar(0); if (modif) return 0; }
    return 1;
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

static int incd;
static unsigned long cdts_s[100];
static unsigned char cdtc_s[100];
static unsigned short cdsv[56 * 20];
static unsigned cddrv;
static int cdfirst, cdlast, cdsel, cdbin, cdvol = 200, cdntr;
static unsigned long cdend;
static unsigned long *cdts;
static unsigned char *cdtc;

static unsigned Cd_Peticion(CDREQ *rq) {
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

static long hsg(const unsigned char *a) {
    return ((long)a[2] * 60 + a[1]) * 75 + a[0] - 150;
}

static int Cd_audio(int t) {
    return !(cdtc[t] & 0x40);
}

static int Cd_pistas(void)
{
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

static int cd_paso(int d) {
    int t = cdsel, n = cdntr;
    while (n--) {
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

static unsigned Cd_Tecla(void)
{
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

static void cd_Boton(int x, int y, const char *g, int focus) {
    char b[8];
    int l = strlen(g), w = (l & 1) ? 5 : 6, p = (w - l) / 2, i;
    for (i = 0; i < w; i++) b[i] = ' ';
    b[w] = 0;
    memcpy(b + p, g, l);
    Boton(x, y, b, focus, H_DLG);
}

static void Cd_Cabecera(int x, int y, const char *g)
{
    char b[8];
    int l = strlen(g), p = (7 - l) / 2, i;
    for (i = 0; i < 7; i++) b[i] = ' ';
    b[7] = 0;
    memcpy(b + p, g, l);
    poner_Txt(x, y, H_DLG, b, 7);
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
    sv = cdsv;
    cdts = cdts_s;
    cdtc = cdtc_s;
    for (r = 0; r <= h; r++)
        for (c = 0; c < w + 2; c++) sv[r * (w + 2) + c] = vid[(y + r) * 80 + x + c];
    Forma_cursor(0);
    Caja(x, y, w, h, H_DLG, "CD Player");

    rg.x.ax = 0x1500; rg.x.bx = 0;
    int86(0x2F, &rg, &rg);
    if (rg.x.bx == 0) {
        poner_Txt(x + 2, y + 1, H_DLG, "MSCDEX is not loaded (CD driver).", w - 4);
        poner_Txt(x + 2, y + 3, H_DLG, "Load MSCDEX or SHSUCDX and try again.", w - 4);
        poner_Txt(x + 2, y + 7, H_DLG, "Press a key", w - 4);
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
        if (!cdntr)
        {
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
        if (cdntr && (playing || paused))
        {
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

        for (r = 2; r <= 9; r++) linea_H(ix, y + r - 1, iw, H_LCD, ' ');
        poner_car(ix, y + 1, H_LCDB, 0xDA); linea_H(ix + 1, y + 1, iw - 2, H_LCDB, 0xC4); poner_car(ix + iw - 1, y + 1, H_LCDB, 0xBF);
        for (r = 3; r <= 8; r++) { poner_car(ix, y + r - 1, H_LCDB, 0xB3); poner_car(ix + iw - 1, y + r - 1, H_LCDB, 0xB3); }
        poner_car(ix, y + 8, H_LCDB, 0xC0); linea_H(ix + 1, y + 8, iw - 2, H_LCDB, 0xC4); poner_car(ix + iw - 1, y + 8, H_LCDB, 0xD9);
        poner_Txt(x + 2, y + 9, H_DLG, "", w - 4);
        if (!cdntr) {
            poner_Txt(lx + 8, y + 3, H_LCD, err ? "NO DISC" : "NOT AUDIO", 14);
            poner_Txt(lx + 8, y + 5, H_LCDD, "Insert an audio CD", 24);
            poner_Txt(x + 2, y + 10, H_DLG, "", w - 4);
            for (r = 12; r <= 14; r++) poner_Txt(x + 2, y + r - 1, H_DLG, "", w - 4);
        } else {
            tot = cdend / 75;
            tl = (int)((cdsel < cdlast ? cdts[cdsel + 1] : cdend) - cdts[cdsel]) / 75;
            poner_Txt(lx, y + 2, H_LCDD, "TRACK", 5);
            poner_Txt(lx + 9, y + 2, H_LCDD, "TIME", 6);
            poner_Txt(lx + 30, y + 2, H_LCDD, "STATUS", 6);
            Cd_Grande(lx, y + 3, cdsel / 10 % 10, H_LCD);
            Cd_Grande(lx + 4, y + 3, cdsel % 10, H_LCD);
            mm = (playing || paused) ? mn : 0;
            if (mm > 99) mm = 99;
            dg = (playing || (paused && blink)) ? H_LCD : H_LCDD;
            Cd_Grande(lx + 9, y + 3, mm / 10, dg);
            Cd_Grande(lx + 13, y + 3, mm % 10, dg);
            poner_car(lx + 17, y + 3, dg, 0xFE);
            poner_car(lx + 17, y + 5, dg, 0xFE);
            Cd_Grande(lx + 19, y + 3, ((playing || paused) ? sc : 0) / 10 % 10, dg);
            Cd_Grande(lx + 23, y + 3, ((playing || paused) ? sc : 0) % 10, dg);
            fmt(t, "%c %s", playing ? 0x10 : paused ? 0xBA : 0xFE,
                playing ? "PLAYING" : paused ? "PAUSED" : "STOPPED");
            poner_Txt(lx + 30, y + 3, H_LCD, t, 15);
            fmt(t, "Track %d of %d", cdsel, cdlast);
            poner_Txt(lx + 30, y + 4, H_LCDD, t, 15);
            fmt(t, "Disc %d:%02d", (int)(tot / 60), (int)(tot % 60));
            poner_Txt(lx + 30, y + 5, H_LCDD, t, 15);

            n = 0;
            if ((playing || paused) && tl > 0) n = (mn * 60 + sc) * 44 / tl;
            if (n > 44) n = 44;
            for (i = 0; i < 44; i++) poner_car(lx + i, y + 7, i < n ? H_LCD : H_LCDD, i < n ? 0xDB : 0xB0);

            n = cdvol * 30 / 255;
            poner_Txt(x + 2, y + 10, H_DLG, " Volume", 8);
            for (i = 0; i < 30; i++) poner_car(x + 10 + i, y + 10, H_DLG, i < n ? 0xDB : 0xB0);
            fmt(t, " %3d%%", cdvol * 100 / 255);
            poner_Txt(x + 40, y + 10, H_DLG, t, w - 42);

            for (i = 0; i < 32; i++) {
                int tn = i + 1, cx0 = x + 3 + (i % 16) * 3, cy0 = y + 12 + i / 16;
                if (tn >= cdfirst && tn <= cdlast) {
                    if (Cd_audio(tn)) fmt(t, " %02d", tn); else strcpy(t, " --");
                    poner_Txt(cx0, cy0, tn == cdsel ? H_SELD : H_DLG, t, 3);
                } else poner_Txt(cx0, cy0, H_DLG, "", 3);
            }
        }

        poner_Txt(x + 2, y + 11, H_DLG, "", w - 4);
        for (r = 15; r <= 17; r++) poner_Txt(x + 2, y + r - 1, H_DLG, "", w - 4);
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

int main(int argc, char **argv) {
    unsigned k;
    int c, r, ok;
    char n[80], t[ELEN + 6];

    borrar_todo();
    Ini_Video();
    Forma_cursor(0);
    if (argc > 1) {
        strncpy(fname, argv[1], 70);
        fname[70] = 0;
        dibujar();
        ok = abrir_Fich(fname);
        if (ok == 0) fmt(msg, "New file");
        else if (ok < 0) fname[0] = 0;
    }
    for (;;) {
        dibujar();
        k = Leer_Tecla();
        msg[0] = 0;
        c = k & 0xFF;
        if (k == K_UP || k == K_DOWN || k == K_LEFT || k == K_RIGHT || k == K_TAB || k == K_STAB || k == K_ENTER)
            mover(k);
        else if (k == K_PGUP) { cr -= VROWS; if (cr < 0) cr = 0; tr -= VROWS; if (tr < 0) tr = 0; }
        else if (k == K_PGDN) { cr += VROWS; if (cr >= NR_) cr = NR_ - 1; tr += VROWS; if (tr > NR_ - VROWS) tr = NR_ - VROWS; }
        else if (k == K_HOME) cc = 0;
        else if (k == K_END) { cc = NC_ - 1; }
        else if (k == K_CHOME) { cc = cr = 0; }
        else if (k == K_DEL || k == K_F8) { if (sh[cr][cc].s) Poner_celda(cc, cr, ""); }
        else if (k == K_F1) Caja_Ayuda();
        else if (k == K_F2) {
            k = editar_celda(0);
            if (k) { Poner_celda(cc, cr, eb); mover(k); }
        }
        else if (k == K_F3) {
            if (modif && !hacer_Salir()) continue;
            strcpy(n, fname);
            if (pedir_Texto("Open", "File name:", n, 70) && n[0]) {
                ok = abrir_Fich(n);
                if (ok == 1) { strcpy(fname, n); cc = cr = tr = lc = 0; fmt(msg, "Opened"); }
                else if (ok == 0) Aviso("Error", "Cannot open file");
            }
        }
        else if (k == K_F4) Hacer_Guardar(1);
        else if (k == K_CTRLS) Hacer_Guardar(0);
        else if (k == K_CTRLP) Repro_cd();
        else if (k == K_F5) {
            strcpy(clip, sh[cr][cc].s ? sh[cr][cc].s : "");
            clipc = cc; clipr = cr; hasclip = 1;
            fmt(msg, "Copied");
        }
        else if (k == K_F6) {
            if (hasclip)
            {
                if (clip[0] == '=') { Mover_refs(clip, t, cc - clipc, cr - clipr); Poner_celda(cc, cr, t); }
                else Poner_celda(cc, cr, clip);
            }
        }
        else if (k == K_F7) {
            n[0] = 0;
            if (pedir_Texto("Go to", "Cell (e.g. C12):", n, 10) && n[0]) {
                ip = n; perr = 0;
                ok = Leer_Ref(&c, &r);
                if (ok && !perr) { cc = c; cr = r; }
                else Aviso("Error", "Invalid cell");
                perr = 0;
            }
        }
        else if (k == K_F9) {
            decm = (decm + 1) & 3; needfit = 1;
            if (decm == 3) fmt(msg, "Decimals: auto");
            else fmt(msg, "Decimals: %d", decm);
        }
        else if (k == K_AA) { if (cw[cc] < 30) cw[cc]++; au[cc] = 0; modif = 1; }
        else if (k == K_AZ) { if (cw[cc] > 4) cw[cc]--; au[cc] = 0; modif = 1; }
        else if (k == K_AS) sumar_auto("SUM");
        else if (k == K_AM) sumar_auto("MUL");
        else if (k == K_AD) sumar_auto("DIV");
        else if (k == K_AP) Hacer_Porcentaje();
        else if (k == K_F10 || k == K_AX) { if (hacer_Salir()) break; }
        else if (k == K_ESC) { if (!modif) break; if (hacer_Salir()) break; }
        else if (c >= 32) {
            k = editar_celda(c);
            if (k) { Poner_celda(cc, cr, eb); mover(k); }
        }
    }
    Fin_Video();
    return 0;
}
