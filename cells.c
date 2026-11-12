/*
 * CELLS - simple spreadsheet for DOS, with the same look as NC
 * OpenWatcom C89, small model. No printf, no floating point (no emulator
 * or 8087 needed): numbers are integers with 2 fixed decimals.
 *
 * Keys: arrows, PgUp/PgDn, Home, Ctrl+Home, Tab, Enter (down)
 *   typing = edit cell, F2 = edit contents, Del/F8 = clear cell
 *   F1 help, F3 open, F4 save as, Ctrl+S save, F5 copy, F6 paste,
 *   F7 go to cell, F9 decimals, F10 quit, Alt+A / Alt+Z column width,
 *   Alt+S sum of the cells above (or to the left)
 * Formulas: =A1+B2*3  (  )  %   SUM(A1:A9)  AVG  MIN  MAX  COUNT
 * Usage: cells [file.hoj]
 */
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
    unsigned char st, e, k;   /* st: 0 dirty 1 calculating 2 ready; k: 0 empty 1 num 2 text 3 formula */
} CELL;

static CELL sh[NR_][NC_];
static int cw[NC_];
static char au[NC_];             /* 1 = automatic width */
static int needfit;
static int cc, cr, tr, lc;       /* cursor, top row and column */
static int decm = 3;             /* 0,1,2 decimals, 3 = auto */
static int modif;
static char fname[80];
static char msg[64];
static char clip[ELEN + 6];
static int clipc, clipr, hasclip;

/* ---------------- video ---------------- */
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

static int vfmt(char *o, const char *f, va_list ap)
{
    static const char hx[] = "0123456789ABCDEF";
    char *o0 = o, tmp[12], *p;
    int left, zero, w, prec, lng, n, neg, base;
    unsigned long v;
    long l;

    while (*f) {
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
        case 'u':
            v = lng ? va_arg(ap, unsigned long) : (unsigned long)va_arg(ap, unsigned);
            goto num;
        case 'x':
        case 'X':
            base = 16;
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

static int fmt(char *o, const char *f, ...)
{
    va_list ap;
    int n;
    va_start(ap, f);
    n = vfmt(o, f, ap);
    va_end(ap);
    return n;
}

static void scur(int x, int y)
{
    union REGS r;
    r.h.ah = 2; r.h.bh = 0; r.h.dh = y; r.h.dl = x;
    int86(0x10, &r, &r);
}

static void cshape(int on)
{
    union REGS r;
    r.h.ah = 1;
    r.x.cx = on ? (mono ? 0x0B0C : 0x0607) : 0x2000;
    int86(0x10, &r, &r);
}

static void blink(int on)
{
    union REGS r;
    r.x.ax = 0x1003; r.h.bl = (unsigned char)on; r.h.bh = 0;
    int86(0x10, &r, &r);
}

static void vinit(void)
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

static void vflush(void)
{
    if (!vdirty) return;
    vdirty = 0;
    if (!mono) {
        while (inp(0x3DA) & 8) ;
        while (!(inp(0x3DA) & 8)) ;
    }
    _fmemcpy(vreal, (void __far *)vbuf, 4000);
}

static void vend(void)
{
    _fmemcpy(vreal, (void __far *)vsave, 4000);
    if (!mono) blink(1);
    cshape(1);
    scur(sx, sy);
}

static void vput(int x, int y, int a, int c)
{
    vdirty = 1;
    vid[y * 80 + x] = ((unsigned)col[a] << 8) | (unsigned char)c;
}

static void hline(int x, int y, int w, int a, int c)
{
    unsigned short __far *p = vid + y * 80 + x;
    unsigned v = ((unsigned)col[a] << 8) | (unsigned char)c;
    vdirty = 1;
    while (w-- > 0) *p++ = v;
}

static void vputsn(int x, int y, int a, const char *s, int w)
{
    unsigned short __far *p = vid + y * 80 + x;
    unsigned at = (unsigned)col[a] << 8;
    vdirty = 1;
    while (w > 0 && *s) { *p++ = at | (unsigned char)*s++; w--; }
    while (w > 0) { *p++ = at | ' '; w--; }
}

static void box(int x, int y, int w, int h, int a, const char *title)
{
    int i;
    char t[70];
    vput(x, y, a, 0xC9); hline(x + 1, y, w - 2, a, 0xCD); vput(x + w - 1, y, a, 0xBB);
    for (i = 1; i < h - 1; i++) {
        vput(x, y + i, a, 0xBA); hline(x + 1, y + i, w - 2, a, ' '); vput(x + w - 1, y + i, a, 0xBA);
    }
    vput(x, y + h - 1, a, 0xC8); hline(x + 1, y + h - 1, w - 2, a, 0xCD); vput(x + w - 1, y + h - 1, a, 0xBC);
    if (title && *title) {
        i = fmt(t, " %.60s ", title);
        vputsn(x + (w - i) / 2, y, a, t, i);
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

static void buttonx(int x, int y, const char *s, int focus, int sh_)
{
    int l = strlen(s);
    vputsn(x, y, focus ? H_BTNF : H_BTN, s, l);
    vput(x + l, y, sh_, 0xDC);
    hline(x + 1, y + 1, l, sh_, 0xDF);
}
#define button(x, y, s, f) buttonx(x, y, s, f, H_DLG)

/* ---------------- keyboard ---------------- */
static unsigned normkey(unsigned k)
{
    if ((k & 0xFF) == 0xE0 && (k >> 8)) k &= 0xFF00;
    else if ((k & 0xFF) == 0) k &= 0xFF00;
    if ((k >> 8) == 0xE0) k = 0x1C00 | (k & 0xFF);
    return k;
}

static unsigned getkey(void)
{
    if (!_bios_keybrd(_KEYBRD_READY)) vflush();
    while (!_bios_keybrd(_KEYBRD_READY)) ;
    return normkey(_bios_keybrd(_KEYBRD_READ));
}

/* ---------------- dialogs ---------------- */
static int askkey(const char *title, const char *l1)
{
    int f = 0, c;
    unsigned k;
    cshape(0);
    for (;;) {
        box(10, 9, 60, 6, H_DLG, title);
        vputsn(12, 10, H_DLG, l1, 56);
        button(21, 12, "  Yes   ", f == 0);
        button(33, 12, "   No   ", f == 1);
        button(45, 12, " Cancel ", f == 2);
        k = getkey();
        c = k & 0xFF;
        if (c == 27) { c = 27; break; }
        if (c == 13) { c = f == 0 ? 'Y' : f == 1 ? 'N' : 27; break; }
        if (k == K_LEFT) f = (f + 2) % 3;
        else if (k == K_RIGHT || c == 9) f = (f + 1) % 3;
        else {
            c = toupper(c);
            if (c == 'Y' || c == 'N') break;
        }
    }
    return c;
}

static void msgbox(const char *title, const char *text)
{
    box(10, 9, 60, 6, H_ERR, title);
    vputsn(12, 10, H_ERR, text, 56);
    buttonx(37, 12, "  Ok  ", 1, H_ERSH);
    getkey();
}

static int inputbox(const char *title, const char *prompt, char *buf, int max)
{
    int l = strlen(buf), cp = l, off, c;
    unsigned k;
    for (;;) {
        box(10, 9, 60, 7, H_DLG, title);
        vputsn(12, 10, H_DLG, prompt, 56);
        off = cp > 53 ? cp - 53 : 0;
        vput(12, 11, H_DLG, '[');
        vputsn(13, 11, H_INP, buf + off, 54);
        vput(67, 11, H_DLG, ']');
        button(23, 13, "  Ok  ", 1);
        button(39, 13, " Cancel ", 0);
        cshape(1);
        scur(13 + cp - off, 11);
        k = getkey();
        c = k & 0xFF;
        if (k == K_LEFT) { if (cp) cp--; }
        else if (k == K_RIGHT) { if (cp < l) cp++; }
        else if (k == K_HOME) cp = 0;
        else if (k == K_END) cp = l;
        else if (k == K_DEL) {
            if (cp < l) { memmove(buf + cp, buf + cp + 1, l - cp); l--; }
        }
        else if (c == 13) { cshape(0); return 1; }
        else if (c == 27) { cshape(0); return 0; }
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

static void cdplayer(void);

static void helpbox(void)
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
    box(7, 1, 66, 23, H_DLG, "Help");
    for (i = 0; i < 17; i++) vputsn(9, 3 + i, H_DLG, t[i], 62);
    getkey();
}

/* ---------------- sheet: calculation ---------------- */
static int perr, depth;
static const char *ip;

static void skipsp(void) { while (*ip == ' ') ip++; }

static long evalcell(int c, int r);
static long expr(void);

static long numtok(int comma)
{
    long v = 0, f = 0;
    int n = 0;
    while (isdigit((unsigned char)*ip)) {
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

/* ip on a letter: reads A1..Z99. returns 0 if it is not a reference */
static int refparse(int *c, int *r)
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

static long addo(long a, long b)
{
    if (b > 0 ? a > LIM - b : a < -LIM - b) { perr = E_OVF; return 0; }
    return a + b;
}

static long mulo(long a, long b)
{
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

static long divo(long a, long b)
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

static void accum(ACC *a, long v)
{
    if (a->mode) {
        if (a->n == 0) a->sum = v;
        else if (a->mode == 1) a->sum = mulo(a->sum, v);
        else if (v != 0) a->sum = divo(a->sum, v);
        a->n++;
        return;
    }
    if (a->n == 0 || v < a->mn) a->mn = v;
    if (a->n == 0 || v > a->mx) a->mx = v;
    a->sum = addo(a->sum, v);
    a->n++;
}

static long func(const char *w)
{
    ACC a;
    int c1, r1, c2, r2, c, r, t;
    const char *sv;
    long v;
    a.sum = 0; a.mn = 0; a.mx = 0; a.n = 0;
    a.mode = !strcmp(w, "MUL") ? 1 : !strcmp(w, "DIV") ? 2 : 0;
    ip++;                       /* ( */
    for (;;) {
        skipsp();
        if (*ip == ')') { ip++; break; }
        sv = ip;
        if (refparse(&c1, &r1) && *ip == ':') {
            ip++;
            if (!refparse(&c2, &r2)) perr = E_SINT;
            if (perr) break;
            if (c1 > c2) { t = c1; c1 = c2; c2 = t; }
            if (r1 > r2) { t = r1; r1 = r2; r2 = t; }
            for (r = r1; r <= r2 && !perr; r++)
                for (c = c1; c <= c2 && !perr; c++) {
                    v = evalcell(c, r);
                    if (!perr && (sh[r][c].k == 1 || sh[r][c].k == 3)) accum(&a, v);
                }
        } else {
            ip = sv;
            v = expr();
            if (!perr) accum(&a, v);
        }
        if (perr) break;
        skipsp();
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

static long primary(void)
{
    long v = 0;
    int c, r, n;
    char w[10];
    skipsp();
    if (*ip == '(') {
        ip++;
        v = expr();
        skipsp();
        if (*ip == ')') ip++; else perr = E_SINT;
    } else if (isdigit((unsigned char)*ip) || *ip == '.') {
        v = numtok(0);
    } else if (isalpha((unsigned char)*ip)) {
        if (refparse(&c, &r)) {
            if (!perr) v = evalcell(c, r);
        } else {
            n = 0;
            while (isalpha((unsigned char)*ip)) {
                if (n < 8) w[n++] = (char)toupper((unsigned char)*ip);
                ip++;
            }
            w[n] = 0;
            skipsp();
            if (*ip == '(') v = func(w); else perr = E_SINT;
        }
    } else {
        perr = E_SINT;
    }
    skipsp();
    while (*ip == '%' && !perr) { ip++; v /= 100; skipsp(); }
    return v;
}

static long unary(void)
{
    skipsp();
    if (*ip == '-') { ip++; return -unary(); }
    if (*ip == '+') { ip++; return unary(); }
    return primary();
}

static long term(void)
{
    long a = unary(), b;
    for (;;) {
        skipsp();
        if (perr) return 0;
        if (*ip == '*') { ip++; b = unary(); a = mulo(a, b); }
        else if (*ip == '/') { ip++; b = unary(); a = divo(a, b); }
        else break;
    }
    return a;
}

static long expr(void)
{
    long a = term(), b;
    for (;;) {
        skipsp();
        if (perr) return 0;
        if (*ip == '+') { ip++; b = term(); a = addo(a, b); }
        else if (*ip == '-') { ip++; b = term(); a = addo(a, -b); }
        else break;
    }
    return a;
}

static long evalcell(int c, int r)
{
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
            v = expr();
            skipsp();
            if (!perr && *ip) perr = E_SINT;
        } else if (*s == '\'') p->k = 2;
        else {
            int neg = 0;
            ip = s;
            skipsp();
            if (*ip == '-') { neg = 1; ip++; } else if (*ip == '+') ip++;
            if (isdigit((unsigned char)*ip) || *ip == '.' || *ip == ',') {
                v = numtok(1);
                if (neg) v = -v;
                skipsp();
                if (*ip == '%') { ip++; v /= 100; skipsp(); }
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

static void invalidate(void)
{
    int r, c;
    for (r = 0; r < NR_; r++)
        for (c = 0; c < NC_; c++) sh[r][c].st = 0;
    needfit = 1;
}

static void setraw(int c, int r, const char *s)
{
    CELL *p = &sh[r][c];
    if (p->s) { free(p->s); p->s = 0; }
    if (s && *s) {
        p->s = (char *)malloc(strlen(s) + 1);
        if (!p->s) fmt(msg, "Out of memory");
        else strcpy(p->s, s);
    }
}

static void setcell(int c, int r, const char *s)
{
    setraw(c, r, s);
    modif = 1;
    invalidate();
}

static void clearall(void)
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

static void fmtnum(char *o, long v)
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

/* copies a formula adjusting the references (for pasting) */
static void adjref(const char *s, char *d, int dc, int dr)
{
    const char *q;
    int c, r, prev = 0;
    while (*s) {
        if (isalpha((unsigned char)*s) && !isalnum(prev)) {
            q = s;
            c = toupper((unsigned char)*q) - 'A'; q++;
            if (isdigit((unsigned char)*q)) {
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

/* ---------------- files ---------------- */
static char rb[512], wb[1024];
static int rpos, rlen, wlen;

static int getln(int fd, char *ln, int max)
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

static int wflush(int fd)
{
    int ok = 1;
    if (wlen && write(fd, wb, wlen) != wlen) ok = 0;
    wlen = 0;
    return ok;
}

static int putln(int fd, const char *s)
{
    int l = strlen(s);
    if (wlen + l + 2 > 1024) if (!wflush(fd)) return 0;
    memcpy(wb + wlen, s, l);
    wlen += l;
    wb[wlen++] = '\r';
    wb[wlen++] = '\n';
    return 1;
}

static int savefile(const char *name)
{
    int fd, r, c, ok = 1;
    char ln[100], t[12];
    fd = open(name, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, S_IREAD | S_IWRITE);
    if (fd < 0) return 0;
    wlen = 0;
    ok = putln(fd, "HOJA 1");
    fmt(ln, "D %d", decm);
    ok = ok && putln(fd, ln);
    strcpy(ln, "W");
    for (c = 0; c < NC_; c++) { fmt(t, " %d", au[c] ? 0 : cw[c]); strcat(ln, t); }
    ok = ok && putln(fd, ln);
    for (r = 0; r < NR_ && ok; r++)
        for (c = 0; c < NC_ && ok; c++)
            if (sh[r][c].s) {
                fmt(ln, "%c%d %.78s", 'A' + c, r + 1, sh[r][c].s);
                ok = putln(fd, ln);
            }
    ok = ok && wflush(fd);
    close(fd);
    return ok;
}

static int loadfile(const char *name)
{
    int fd, c, r, n;
    char ln[100];
    const char *q;
    fd = open(name, O_RDONLY | O_BINARY);
    if (fd < 0) return 0;
    rpos = rlen = 0;
    clearall();
    while (getln(fd, ln, 100)) {
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
        if (refparse(&c, &r) && !perr && *ip == ' ') setraw(c, r, ip + 1);
        perr = 0;
    }
    close(fd);
    modif = 0;
    invalidate();
    return 1;
}

/* ---------------- screen ---------------- */
static int lastvis(int l)
{
    int x = 3, c = l;
    while (c < NC_ && x + cw[c] <= 80) { x += cw[c]; c++; }
    return c > l ? c - 1 : l;
}

static void ensure(void)
{
    if (cr < tr) tr = cr;
    if (cr >= tr + VROWS) tr = cr - VROWS + 1;
    if (cc < lc) lc = cc;
    while (cc > lastvis(lc)) lc++;
}

static void refname(char *o, int c, int r)
{
    fmt(o, "%c%d", 'A' + c, r + 1);
}

static void drawcell(int x, int y, int w, int c, int r, int cur)
{
    CELL *p = &sh[r][c];
    char t[48], o[48];
    int a = cur ? H_CUR : H_CELL, l, i;
    perr = 0;
    evalcell(c, r);
    perr = 0;
    if (p->k == 2) {
        vputsn(x, y, a, (p->s[0] == '\'') ? p->s + 1 : p->s, w);
        return;
    }
    if (p->k == 0) { vputsn(x, y, a, "", w); return; }
    if (p->e) {
        strcpy(t, errn[p->e]);
        if (!cur) a = H_ERRV;
    } else fmtnum(t, p->v);
    l = strlen(t);
    if (l > w) { for (i = 0; i < w; i++) o[i] = '#'; o[w] = 0; }
    else { memset(o, ' ', w - l); strcpy(o + w - l, t); }
    vputsn(x, y, a, o, w);
}

static void drawkeys(void)
{
    static const char *lab[10] = { "Help","Edit","Open","Save","Copy","Paste","Go to","Delete","Decim.","Quit" };
    int i;
    char n[4];
    for (i = 0; i < 10; i++) {
        fmt(n, "%2d", i + 1);
        vputsn(i * 8, 24, H_KEYN, n, 2);
        vputsn(i * 8 + 2, 24, H_KEYL, lab[i], 6);
    }
}

static void fitall(void)
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
            perr = 0; evalcell(c, r); perr = 0;
            if (p->k == 2) l = strlen(p->s) - (p->s[0] == '\'');
            else if (p->e) l = strlen(errn[p->e]);
            else { fmtnum(t, p->v); l = strlen(t); }
            if (l > m) m = l;
        }
        m++;
        cw[c] = m < 8 ? 8 : (m > 30 ? 30 : m);
    }
}

static void draw(void)
{
    int y, x, c, l, last, w;
    char t[100], o[48];
    CELL *p;

    if (needfit) fitall();
    ensure();
    last = lastvis(lc);
    /* formula bar */
    refname(t, cc, cr);
    fmt(o, " %-5s", t);
    vputsn(0, 0, H_BAR, o, 7);
    p = &sh[cr][cc];
    vputsn(7, 0, H_CELL, p->s ? p->s : "", 73);
    /* column header */
    vputsn(0, 1, H_HDR, "", 3);
    x = 3;
    for (c = lc; c <= last; c++) {
        w = cw[c];
        memset(o, ' ', w); o[w] = 0;
        o[w / 2] = (char)('A' + c);
        vputsn(x, 1, c == cc ? H_HDRC : H_HDR, o, w);
        x += w;
    }
    if (x < 80) hline(x, 1, 80 - x, H_HDR, ' ');
    /* rows */
    for (y = 0; y < VROWS; y++) {
        int r = tr + y;
        if (r >= NR_) { hline(0, 2 + y, 80, H_CELL, ' '); continue; }
        fmt(t, "%3d", r + 1);
        vputsn(0, 2 + y, r == cr ? H_HDRC : H_HDR, t, 3);
        x = 3;
        for (c = lc; c <= last; c++) {
            drawcell(x, 2 + y, cw[c] - 1, c, r, c == cc && r == cr);
            vput(x + cw[c] - 1, 2 + y, H_LINE, 0xB3);
            x += cw[c];
        }
        if (x < 80) hline(x, 2 + y, 80 - x, H_CELL, ' ');
    }
    /* status line */
    p = &sh[cr][cc];
    perr = 0;
    evalcell(cc, cr);
    perr = 0;
    l = fmt(t, " %s%s", fname[0] ? fname : "(no name)", modif ? " *" : "");
    hline(0, 23, 80, H_STAT, ' ');
    vputsn(0, 23, H_STAT, t, 30);
    if (msg[0]) vputsn(30, 23, H_STAT, msg, 50);
    else if (p->k == 3 || p->k == 1) {
        if (p->e) fmt(t, "= %s", errn[p->e]);
        else { strcpy(t, "= "); fmtnum(t + 2, p->v); }
        vputsn(30, 23, H_STAT, t, 50);
    }
    drawkeys();
}

/* edits the current cell in the top bar. returns the key that ended it (0 = Esc) */
static char eb[ELEN + 2];

static unsigned editcell(int first)
{
    int l, cp, off, c, typing = first != 0;
    unsigned k;
    char t[12];
    if (first) { eb[0] = (char)first; eb[1] = 0; }
    else { strcpy(eb, sh[cr][cc].s ? sh[cr][cc].s : ""); }
    l = strlen(eb); cp = l;
    cshape(1);
    for (;;) {
        draw();
        refname(t, cc, cr);
        vputsn(0, 0, H_BAR, " ", 7);
        vputsn(1, 0, H_BAR, t, 6);
        off = cp > 71 ? cp - 71 : 0;
        vputsn(7, 0, H_EDIT, eb + off, 73);
        scur(7 + cp - off, 0);
        k = getkey();
        c = k & 0xFF;
        if (k == K_ENTER || k == K_UP || k == K_DOWN || k == K_TAB || k == K_STAB ||
            (typing && (k == K_LEFT || k == K_RIGHT))) {
            cshape(0);
            return k;
        }
        if (c == 27) { cshape(0); return 0; }
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

static void domove(unsigned k)
{
    if (k == K_ENTER || k == K_DOWN) { if (cr < NR_ - 1) cr++; }
    else if (k == K_UP) { if (cr) cr--; }
    else if (k == K_RIGHT || k == K_TAB) { if (cc < NC_ - 1) cc++; }
    else if (k == K_LEFT || k == K_STAB) { if (cc) cc--; }
}

static int numcell(int c, int r)
{
    perr = 0;
    evalcell(c, r);
    perr = 0;
    return sh[r][c].k == 1 || sh[r][c].k == 3;
}

static void autoop(const char *fn)
{
    int r, c, top = -1;
    char t[40], a[8], b[8];
    for (r = 0; r < cr; r++) if (numcell(cc, r)) { top = r; break; }
    if (top >= 0) {
        refname(a, cc, top); refname(b, cc, cr - 1);
    } else {
        for (c = 0; c < cc; c++) if (numcell(c, cr)) { top = c; break; }
        if (top < 0) { fmt(msg, "Nothing to calculate"); return; }
        refname(a, top, cr); refname(b, cc - 1, cr);
    }
    fmt(t, "=%s(%s:%s)", fn, a, b);
    setcell(cc, cr, t);
}

static void dopercent(void)
{
    char o[12], p[12], t[30];
    o[0] = 0; p[0] = 0;
    if (!inputbox("Percentage", "Source cell (e.g. B3):", o, 8) || !o[0]) return;
    if (!inputbox("Percentage", "Percentage (e.g. 20):", p, 8) || !p[0]) return;
    fmt(t, "=%s*%s%%", o, p);
    setcell(cc, cr, t);
}

static char csvsep = ';';

static int iscsv(const char *n)
{
    int l = strlen(n);
    return l > 4 && n[l - 4] == '.' && toupper((unsigned char)n[l - 3]) == 'C' &&
           toupper((unsigned char)n[l - 2]) == 'S' && toupper((unsigned char)n[l - 1]) == 'V';
}

static void setfield(int c, int r, char *f, int n)
{
    char t[ELEN + 4];
    while (n > 0 && f[n - 1] == ' ') n--;
    f[n] = 0;
    if (!n) return;
    if (f[0] == '=') { t[0] = '\''; strcpy(t + 1, f); setraw(c, r, t); }
    else setraw(c, r, f);
}

static int csvload(const char *name, const char *spec)
{
    int fd, r = 0, c, n, q, nw = 0, w[NC_], fixed, len, k;
    char ln[200], f[ELEN + 2];
    const char *s, *p;
    fixed = isdigit((unsigned char)spec[0]);
    if (fixed) {
        p = spec;
        while (*p && nw < NC_) {
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
    clearall();
    while (r < NR_ && getln(fd, ln, 200)) {
        s = ln;
        if (fixed) {
            len = strlen(ln);
            k = 0;
            for (c = 0; c < nw && c < NC_ && k < len; c++) {
                n = 0;
                while (k < len && n < w[c]) { if (n < ELEN) f[n] = ln[k]; n++; k++; }
                if (n > ELEN) n = ELEN;
                q = 0;
                while (q < n && f[q] == ' ') q++;
                memmove(f, f + q, n - q);
                setfield(c, r, f, n - q);
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
                setfield(c, r, f, n);
                c++;
                if (*s == csvsep) s++; else break;
            }
        }
        r++;
    }
    close(fd);
    modif = 0;
    invalidate();
    return 1;
}

static int putraw(int fd, const char *s)
{
    int l = strlen(s);
    if (wlen + l > 1000) if (!wflush(fd)) return 0;
    memcpy(wb + wlen, s, l);
    wlen += l;
    return 1;
}

static int csvsave(const char *name)
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
            perr = 0; evalcell(c, r); perr = 0;
            if (c) ok = putraw(fd, sp);
            if (sh[r][c].k == 2) {
                s = sh[r][c].s[0] == '\'' ? sh[r][c].s + 1 : sh[r][c].s;
                if (strchr(s, csvsep) || strchr(s, '"')) {
                    char *d = t;
                    ok = ok && putraw(fd, "\"");
                    while (*s && ok) {
                        d = t;
                        while (*s && d < t + 40) { if (*s == '"') *d++ = '"'; *d++ = *s++; }
                        *d = 0;
                        ok = putraw(fd, t);
                    }
                    ok = ok && putraw(fd, "\"");
                } else ok = ok && putraw(fd, s);
            } else if (sh[r][c].k) {
                if (sh[r][c].e) strcpy(t, errn[sh[r][c].e]);
                else {
                    char *d;
                    fmtnum(t, sh[r][c].v);
                    if (csvsep == ';') for (d = t; *d; d++) if (*d == '.') *d = ',';
                }
                ok = ok && putraw(fd, t);
            }
        }
        ok = ok && putraw(fd, "\r\n");
    }
    decm = sd;
    ok = ok && wflush(fd);
    close(fd);
    return ok;
}

/* 1 = opened, 0 = error, -1 = cancelled */
static int openany(const char *name)
{
    char spec[40];
    int fd;
    if (!iscsv(name)) return loadfile(name);
    fd = open(name, O_RDONLY | O_BINARY);
    if (fd < 0) return 0;
    close(fd);
    strcpy(spec, ";");
    if (!inputbox("Open CSV", "Separator (; , tab) or fixed widths (e.g. 10,5,8):", spec, 38)) return -1;
    return csvload(name, spec);
}

static void dosave(int ask)
{
    char n[80];
    if (ask || !fname[0]) {
        strcpy(n, fname[0] ? fname : "SHEET1.HOJ");
        if (!inputbox("Save", "File name:", n, 70)) return;
        if (!n[0]) return;
        strcpy(fname, n);
    }
    if (iscsv(fname) ? csvsave(fname) : savefile(fname)) { modif = 0; fmt(msg, "Saved"); }
    else msgbox("Error", "Cannot save file");
}

static int doexit(void)
{
    int a;
    if (!modif) return 1;
    a = askkey("Quit", "Save changes before quitting?");
    if (a == 27) return 0;
    if (a == 'Y') { dosave(0); if (modif) return 0; }
    return 1;
}

/* ---------------- CD player (Ctrl+P) ----------------
 * Uses MSCDEX (INT 2Fh): the drive itself plays the audio and NC only
 * sends it commands, so the music keeps playing even if you close the window
 * or run programs. MSCDEX or SHSUCDX must be loaded and the drive
 * connected with the audio cable to the sound card.
 */
#pragma pack(1)
typedef struct {
    unsigned char len, unit, cmd;
    unsigned status;
    unsigned char res[8];
    unsigned char media;        /* ioctl: descriptor; play: 0 = HSG address */
    unsigned long addr;         /* ioctl: pointer to the block; play: start sector */
    unsigned long num;          /* ioctl: bytes; play: number of sectors */
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

static unsigned cdreq(CDREQ *rq)
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

/* IOCTL: out=0 reads, out=1 writes; cb is the control block */
static unsigned cdctl(int out, unsigned char *cb, unsigned n)
{
    CDREQ rq;
    memset(&rq, 0, sizeof rq);
    rq.len = 26;
    rq.cmd = out ? 12 : 3;
    rq.addr = (unsigned long)(void __far *)cb;
    rq.num = n;
    return cdreq(&rq);
}

/* commands without data: 133 = stop/pause, 136 = resume */
static void cdsimple(int cmd)
{
    CDREQ rq;
    memset(&rq, 0, sizeof rq);
    rq.len = 13;
    rq.cmd = (unsigned char)cmd;
    cdreq(&rq);
}

static long hsg(const unsigned char *a)
{
    return ((long)a[2] * 60 + a[1]) * 75 + a[0] - 150;
}

static int cdaudio(int t)
{
    return !(cdtc[t] & 0x40);
}

/* reads the disc index; returns the number of tracks or 0 */
static int cdtoc(void)
{
    unsigned char cb[8];
    int t;
    cb[0] = 10;
    if (cdctl(0, cb, 7) & 0x8000) return 0;
    cdfirst = cb[1];
    cdlast = cb[2];
    if (cdfirst < 1 || cdlast > 99 || cdlast < cdfirst) return 0;
    cdend = hsg(cb + 3);
    for (t = cdfirst; t <= cdlast; t++) {
        cb[0] = 11;
        cb[1] = (unsigned char)t;
        if (cdctl(0, cb, 7) & 0x8000) return 0;
        cdts[t] = hsg(cb + 2);
        cdtc[t] = cb[6];
    }
    return cdlast - cdfirst + 1;
}

/* plays from track t to the end of the disc */
static void cdplay(int t)
{
    CDREQ rq;
    memset(&rq, 0, sizeof rq);
    rq.len = 22;
    rq.cmd = 132;
    rq.media = 0;
    rq.addr = cdts[t];
    rq.num = cdend - cdts[t];
    cdreq(&rq);
}

static void cdsetvol(void)
{
    unsigned char cb[9];
    cb[0] = 3;
    cb[1] = 0; cb[2] = (unsigned char)cdvol;
    cb[3] = 1; cb[4] = (unsigned char)cdvol;
    cb[5] = 2; cb[6] = 0;
    cb[7] = 3; cb[8] = 0;
    cdctl(1, cb, 9);
}

/* next audio track in direction d */
static int cdstep(int d)
{
    int t = cdsel, n = cdntr;
    while (n--) {
        t += d;
        if (t > cdlast) t = cdfirst;
        if (t < cdfirst) t = cdlast;
        if (cdaudio(t)) return t;
    }
    return cdsel;
}

/* the Q subcode comes in BCD in some drivers and in binary in others:
 * if a value that is not BCD shows up it is converted to binary */
static int bcdok(unsigned char b)
{
    return (b >> 4) < 10 && (b & 15) < 10;
}

static int cdval(unsigned char b)
{
    if (!bcdok(b)) { cdbin = 1; return b; }
    return cdbin ? b : (b >> 4) * 10 + (b & 15);
}

static int cdtrack(unsigned char b)
{
    /* the track number can come in BCD or binary (0x10 = 10 or 16):
       if both are valid, the one closest to the current track is chosen */
    int bin = b, bcd = bcdok(b) ? (b >> 4) * 10 + (b & 15) : -1;
    int vb = bin >= cdfirst && bin <= cdlast, vd = bcd >= cdfirst && bcd <= cdlast;
    if (vb && vd && bin != bcd)
        return abs(bin - cdsel) <= abs(bcd - cdsel) ? bin : bcd;
    if (vb) return bin;
    if (vd) return bcd;
    return bin;
}

/* waits for a key; returns 0 every second to refresh */
static unsigned cdkey(void)
{
    unsigned __far *tick = (unsigned __far *)MK_FP(0x40, 0x6C);
    unsigned last = *tick;
    vflush();
    while (!_bios_keybrd(_KEYBRD_READY))
        if (*tick - last >= 18) return 0;
    return normkey(_bios_keybrd(_KEYBRD_READ));
}

/* big 3x3 digit with half blocks (DB = full, DF = top, DC = bottom) */
#define BF "\xDB"
#define BU "\xDF"
#define BD "\xDC"
static void cdbig(int x, int y, int d, int a)
{
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
    vputsn(x, y, a, sg[d][0], 3);
    vputsn(x, y + 1, a, sg[d][1], 3);
    vputsn(x, y + 2, a, sg[d][2], 3);
}

/* 7-column button with the symbol centered and a shadow */
static void cdbtn(int x, int y, const char *g, int focus)
{
    char b[8];
    int l = strlen(g), w = (l & 1) ? 5 : 6, p = (w - l) / 2, i;
    for (i = 0; i < w; i++) b[i] = ' ';
    b[w] = 0;
    memcpy(b + p, g, l);
    buttonx(x, y, b, focus, H_DLG);
}

static void cdcap(int x, int y, const char *g)
{
    char b[8];
    int l = strlen(g), p = (7 - l) / 2, i;
    for (i = 0; i < 7; i++) b[i] = ' ';
    b[7] = 0;
    memcpy(b + p, g, l);
    vputsn(x, y, H_DLG, b, 7);
}

static void cdplayer(void)
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
    cshape(0);
    box(x, y, w, h, H_DLG, "CD Player");

    rg.x.ax = 0x1500; rg.x.bx = 0;
    int86(0x2F, &rg, &rg);
    if (rg.x.bx == 0) {
        vputsn(x + 2, y + 1, H_DLG, "MSCDEX is not loaded (CD driver).", w - 4);
        vputsn(x + 2, y + 3, H_DLG, "Load MSCDEX or SHSUCDX and try again.", w - 4);
        vputsn(x + 2, y + 7, H_DLG, "Press a key", w - 4);
        do k = cdkey(); while (!k);
        done = 1;
    } else {
        cddrv = rg.x.cx;
        cdntr = 0;
        cdsel = 0;
        cb[0] = 4;
        if (!(cdctl(0, cb, 9) & 0x8000)) cdvol = cb[2];
    }

    while (!done) {
        if (!cdntr) {
            cdntr = cdtoc();
            if (cdntr) {
                for (i = cdfirst; i <= cdlast; i++) if (cdaudio(i)) break;
                cdsel = i > cdlast ? cdfirst : i;
            }
        }
        cb[0] = 15;
        st = cdctl(0, cb, 11);
        err = (st & 0x8000) != 0;
        playing = !err && (st & 0x200) != 0;
        paused = !err && !playing && (cb[1] & 1);
        if (cdntr && (playing || paused)) {
            cb[0] = 12;
            if (!(cdctl(0, cb, 11) & 0x8000)) {
                trk = cdtrack(cb[2]);
                mn = cdval(cb[4]);
                sc = cdval(cb[5]);
                if (hold) hold--;
                else if (trk >= cdfirst && trk <= cdlast) cdsel = trk;
            }
        }
        blink ^= 1;
        lx = ix + 3;
        /* black LCD screen */
        for (r = 2; r <= 9; r++) hline(ix, y + r - 1, iw, H_LCD, ' ');
        vput(ix, y + 1, H_LCDB, 0xDA); hline(ix + 1, y + 1, iw - 2, H_LCDB, 0xC4); vput(ix + iw - 1, y + 1, H_LCDB, 0xBF);
        for (r = 3; r <= 8; r++) { vput(ix, y + r - 1, H_LCDB, 0xB3); vput(ix + iw - 1, y + r - 1, H_LCDB, 0xB3); }
        vput(ix, y + 8, H_LCDB, 0xC0); hline(ix + 1, y + 8, iw - 2, H_LCDB, 0xC4); vput(ix + iw - 1, y + 8, H_LCDB, 0xD9);
        vputsn(x + 2, y + 9, H_DLG, "", w - 4);
        if (!cdntr) {
            vputsn(lx + 8, y + 3, H_LCD, err ? "NO DISC" : "NOT AUDIO", 14);
            vputsn(lx + 8, y + 5, H_LCDD, "Insert an audio CD", 24);
            vputsn(x + 2, y + 10, H_DLG, "", w - 4);
            for (r = 12; r <= 14; r++) vputsn(x + 2, y + r - 1, H_DLG, "", w - 4);
        } else {
            tot = cdend / 75;
            tl = (int)((cdsel < cdlast ? cdts[cdsel + 1] : cdend) - cdts[cdsel]) / 75;
            vputsn(lx, y + 2, H_LCDD, "TRACK", 5);
            vputsn(lx + 9, y + 2, H_LCDD, "TIME", 6);
            vputsn(lx + 30, y + 2, H_LCDD, "STATUS", 6);
            cdbig(lx, y + 3, cdsel / 10 % 10, H_LCD);
            cdbig(lx + 4, y + 3, cdsel % 10, H_LCD);
            mm = (playing || paused) ? mn : 0;
            if (mm > 99) mm = 99;
            dg = (playing || (paused && blink)) ? H_LCD : H_LCDD;
            cdbig(lx + 9, y + 3, mm / 10, dg);
            cdbig(lx + 13, y + 3, mm % 10, dg);
            vput(lx + 17, y + 3, dg, 0xFE);
            vput(lx + 17, y + 5, dg, 0xFE);
            cdbig(lx + 19, y + 3, ((playing || paused) ? sc : 0) / 10 % 10, dg);
            cdbig(lx + 23, y + 3, ((playing || paused) ? sc : 0) % 10, dg);
            fmt(t, "%c %s", playing ? 0x10 : paused ? 0xBA : 0xFE,
                playing ? "PLAYING" : paused ? "PAUSED" : "STOPPED");
            vputsn(lx + 30, y + 3, H_LCD, t, 15);
            fmt(t, "Track %d of %d", cdsel, cdlast);
            vputsn(lx + 30, y + 4, H_LCDD, t, 15);
            fmt(t, "Disc %d:%02d", (int)(tot / 60), (int)(tot % 60));
            vputsn(lx + 30, y + 5, H_LCDD, t, 15);
            /* track progress */
            n = 0;
            if ((playing || paused) && tl > 0) n = (mn * 60 + sc) * 44 / tl;
            if (n > 44) n = 44;
            for (i = 0; i < 44; i++) vput(lx + i, y + 7, i < n ? H_LCD : H_LCDD, i < n ? 0xDB : 0xB0);
            /* volume */
            n = cdvol * 30 / 255;
            vputsn(x + 2, y + 10, H_DLG, " Volume", 8);
            for (i = 0; i < 30; i++) vput(x + 10 + i, y + 10, H_DLG, i < n ? 0xDB : 0xB0);
            fmt(t, " %3d%%", cdvol * 100 / 255);
            vputsn(x + 40, y + 10, H_DLG, t, w - 42);
            /* tracks */
            for (i = 0; i < 32; i++) {
                int tn = i + 1, cx0 = x + 3 + (i % 16) * 3, cy0 = y + 12 + i / 16;
                if (tn >= cdfirst && tn <= cdlast) {
                    if (cdaudio(tn)) fmt(t, " %02d", tn); else strcpy(t, " --");
                    vputsn(cx0, cy0, tn == cdsel ? H_SELD : H_DLG, t, 3);
                } else vputsn(cx0, cy0, H_DLG, "", 3);
            }
        }
        /* buttons */
        vputsn(x + 2, y + 11, H_DLG, "", w - 4);
        for (r = 15; r <= 17; r++) vputsn(x + 2, y + r - 1, H_DLG, "", w - 4);
        cdbtn(x + 3, y + 15, "\x11\x11", 0);
        cdbtn(x + 11, y + 15, "\x10", playing);
        cdbtn(x + 19, y + 15, "\xFE\xFE", paused);
        cdbtn(x + 27, y + 15, "\xFE", cdntr && !playing && !paused);
        cdbtn(x + 35, y + 15, "\x10\x10", 0);
        cdbtn(x + 43, y + 15, "\x1E", 0);

        k = cdkey();
        if (!k) continue;
        c = (k & 0xFF) ? toupper(k & 0xFF) : 0;
        if (k == K_ESC) done = 1;
        else if (c == ' ' || c == 'P') {
            if (playing) cdsimple(133);
            else if (paused) cdsimple(136);
            else if (cdntr) cdplay(cdsel);
        } else if (k == K_ENTER) {
            if (playing || paused) { cdsimple(133); cdsimple(133); }
            else if (cdntr) cdplay(cdsel);
        }
        else if (k == K_LEFT || k == K_RIGHT || k == K_PGUP || k == K_PGDN) {
            if (cdntr) {
                cdsel = cdstep((k == K_RIGHT || k == K_PGDN) ? 1 : -1);
                if (playing || paused) { cdsimple(133); cdsimple(133); cdplay(cdsel); hold = 2; }
            }
        } else if (c >= '1' && c <= '9') {
            if (cdntr && c - '0' >= cdfirst && c - '0' <= cdlast && cdaudio(c - '0')) {
                cdsel = c - '0';
                cdsimple(133); cdsimple(133); cdplay(cdsel); hold = 2;
            }
        } else if (k == K_UP || k == K_DOWN || c == '+' || c == '-' || c == '=') {
            cdvol += (k == K_UP || c == '+' || c == '=') ? 16 : -16;
            if (cdvol > 255) cdvol = 255;
            if (cdvol < 0) cdvol = 0;
            cdsetvol();
        } else if (c == 'E') {
            cb[0] = 0; cdctl(1, cb, 1);
            cdntr = 0;
        } else if (c == 'C') {
            cb[0] = 5; cdctl(1, cb, 1);
            cdntr = 0;
        }
    }

    vdirty = 1;
    for (r = 0; r <= h; r++)
        for (c = 0; c < w + 2; c++) vid[(y + r) * 80 + x + c] = sv[r * (w + 2) + c];
    vflush();
    rg.h.ah = 1; rg.x.cx = cx;
    int86(0x10, &rg, &rg);
    rg.h.ah = 2; rg.h.bh = 0; rg.x.dx = dx;
    int86(0x10, &rg, &rg);
    incd = 0;
}

int main(int argc, char **argv)
{
    unsigned k;
    int c, r, ok;
    char n[80], t[ELEN + 6];

    clearall();
    vinit();
    cshape(0);
    if (argc > 1) {
        strncpy(fname, argv[1], 70);
        fname[70] = 0;
        draw();
        ok = openany(fname);
        if (ok == 0) fmt(msg, "New file");
        else if (ok < 0) fname[0] = 0;
    }
    for (;;) {
        draw();
        k = getkey();
        msg[0] = 0;
        c = k & 0xFF;
        if (k == K_UP || k == K_DOWN || k == K_LEFT || k == K_RIGHT || k == K_TAB || k == K_STAB || k == K_ENTER)
            domove(k);
        else if (k == K_PGUP) { cr -= VROWS; if (cr < 0) cr = 0; tr -= VROWS; if (tr < 0) tr = 0; }
        else if (k == K_PGDN) { cr += VROWS; if (cr >= NR_) cr = NR_ - 1; tr += VROWS; if (tr > NR_ - VROWS) tr = NR_ - VROWS; }
        else if (k == K_HOME) cc = 0;
        else if (k == K_END) { cc = NC_ - 1; }
        else if (k == K_CHOME) { cc = cr = 0; }
        else if (k == K_DEL || k == K_F8) { if (sh[cr][cc].s) setcell(cc, cr, ""); }
        else if (k == K_F1) helpbox();
        else if (k == K_F2) {
            k = editcell(0);
            if (k) { setcell(cc, cr, eb); domove(k); }
        }
        else if (k == K_F3) {
            if (modif && !doexit()) continue;
            strcpy(n, fname);
            if (inputbox("Open", "File name:", n, 70) && n[0]) {
                ok = openany(n);
                if (ok == 1) { strcpy(fname, n); cc = cr = tr = lc = 0; fmt(msg, "Opened"); }
                else if (ok == 0) msgbox("Error", "Cannot open file");
            }
        }
        else if (k == K_F4) dosave(1);
        else if (k == K_CTRLS) dosave(0);
        else if (k == K_CTRLP) cdplayer();
        else if (k == K_F5) {
            strcpy(clip, sh[cr][cc].s ? sh[cr][cc].s : "");
            clipc = cc; clipr = cr; hasclip = 1;
            fmt(msg, "Copied");
        }
        else if (k == K_F6) {
            if (hasclip) {
                if (clip[0] == '=') { adjref(clip, t, cc - clipc, cr - clipr); setcell(cc, cr, t); }
                else setcell(cc, cr, clip);
            }
        }
        else if (k == K_F7) {
            n[0] = 0;
            if (inputbox("Go to", "Cell (e.g. C12):", n, 10) && n[0]) {
                ip = n; perr = 0;
                ok = refparse(&c, &r);
                if (ok && !perr) { cc = c; cr = r; }
                else msgbox("Error", "Invalid cell");
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
        else if (k == K_AS) autoop("SUM");
        else if (k == K_AM) autoop("MUL");
        else if (k == K_AD) autoop("DIV");
        else if (k == K_AP) dopercent();
        else if (k == K_F10 || k == K_AX) { if (doexit()) break; }
        else if (k == K_ESC) { if (!modif) break; if (doexit()) break; }
        else if (c >= 32) {
            k = editcell(c);
            if (k) { setcell(cc, cr, eb); domove(k); }
        }
    }
    vend();
    return 0;
}
