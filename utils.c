/*
 * UTILS - utilities for NC (run from the Utils menu, keeping NC in the background)
 *   utils -agenda          calendar with notes (saved in AGENDA.TXT next to UTILS)
 *   utils -ascii           ASCII table
 *   utils -diff a b        compare two text files, side by side
 * OpenWatcom C89, small model. No printf or floating point.
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
#include <malloc.h>
#include <sys/types.h>
#include <sys/stat.h>

#define K_UP    0x4800
#define K_DOWN  0x5000
#define K_LEFT  0x4B00
#define K_RIGHT 0x4D00
#define K_PGUP  0x4900
#define K_PGDN  0x5100
#define K_HOME  0x4700
#define K_END   0x4F00
#define K_DEL   0x5300
#define K_INS   0x5200
#define K_F3    0x3D00
#define K_F7    0x4100
#define K_F8    0x4200
#define K_F10   0x4400
#define K_CPGUP 0x8400
#define K_CPGDN 0x7600
#define K_TAB   0x0F09
#define K_ENTER 0x1C0D
#define K_ESC   0x011B

/* ---------------- video ---------------- */
enum { H_DLG, H_INP, H_BTN, H_BTNF, H_ERR, H_ERSH, U_SEL, U_HOT, U_TODAY, U_TXT, U_DEL, U_INS, U_CHG,
       U_HDR, U_KEYN, U_KEYL, U_SEP, U_CHGHI, U_NOTE, U_DAYF };
static unsigned char colc[] = { 0x30,0x0F,0x70,0x2F,0x4F,0x40,0x0F,0x3E,0x4F,0x1F,0x4F,0x2F,0x5F,0x30,0x07,0x30,0x19,0x5E,0x3F,0x1F };
static unsigned char colm[] = { 0x70,0x07,0x07,0x0F,0x70,0x70,0x07,0x78,0x0F,0x07,0x70,0x0F,0x70,0x70,0x07,0x70,0x07,0x0F,0x70,0x07 };
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


/* ---------------- text files ---------------- */
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

static char udir[80];      /* directory of UTILS.EXE */

/* ======================= AGENDA ======================= */
#define ELEN  50
#define MAXN  200
#define MAXE  50
#define MAXC  60
#define PER   11            /* visible lines per day */

typedef struct { long key; char t[ELEN + 2]; } NOTE;
typedef struct { long s, e; char t[ELEN + 2]; char w[62]; } EVENT;   /* w = guests separated by ", " */
typedef struct { char n[24]; char ph[18]; } CONT;
typedef struct { int kind, idx; } ITEM;                              /* kind 0 note, 1 event */
static NOTE *notes;
static EVENT *evs;
static CONT *cts;
static int nn, ne, nct;

static const char *mname[12] = { "January", "February", "March", "April", "May", "June", "July",
                                 "August", "September", "October", "November", "December" };

static int leap(int y) { return (y % 4 == 0 && y % 100 != 0) || y % 400 == 0; }

static int mdays(int y, int m)
{
    static const char d[12] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 };
    return (m == 2 && leap(y)) ? 29 : d[m - 1];
}

/* 0 = Monday */
static int dow(int y, int m, int d)
{
    static const int t[12] = { 0, 3, 2, 5, 0, 3, 5, 1, 4, 6, 2, 4 };
    int w;
    if (m < 3) y--;
    w = (y + y / 4 - y / 100 + y / 400 + t[m - 1] + d) % 7;
    return (w + 6) % 7;
}

static long mkkey(int y, int m, int d) { return (long)y * 10000L + m * 100 + d; }

static void apath(char *o)
{
    fmt(o, "%sAGENDA.TXT", udir);
}

static void loadnotes(void)
{
    char p[100], ln[130], *q;
    int fd;
    long k;
    apath(p);
    fd = open(p, O_RDONLY | O_BINARY);
    if (fd < 0) return;
    rpos = rlen = 0;
    while (getln(fd, ln, 130)) {
        if (ln[0] == 'E' && ln[1] == ' ' && ne < MAXE && strlen(ln) > 20) {
            evs[ne].s = atol(ln + 2);
            evs[ne].e = atol(ln + 11);
            q = strrchr(ln + 20, '|');
            evs[ne].w[0] = 0;
            if (q) { *q++ = 0; strncpy(evs[ne].w, q, 60); evs[ne].w[60] = 0; }
            strncpy(evs[ne].t, ln + 20, ELEN);
            evs[ne].t[ELEN] = 0;
            ne++;
        } else if (ln[0] == 'C' && ln[1] == ' ' && nct < MAXC) {
            q = strchr(ln + 2, ';');
            cts[nct].ph[0] = 0;
            if (q) { *q++ = 0; strncpy(cts[nct].ph, q, 16); cts[nct].ph[16] = 0; }
            strncpy(cts[nct].n, ln + 2, 22);
            cts[nct].n[22] = 0;
            nct++;
        } else if (nn < MAXN) {
            k = atol(ln);
            if (k < 19800101L || ln[8] != ' ') continue;
            notes[nn].key = k;
            strncpy(notes[nn].t, ln + 9, ELEN);
            notes[nn].t[ELEN] = 0;
            nn++;
        }
    }
    close(fd);
}

static int savenotes(void)
{
    char p[100], ln[160];
    int fd, i, ok = 1;
    apath(p);
    fd = open(p, O_WRONLY | O_CREAT | O_TRUNC | O_BINARY, S_IREAD | S_IWRITE);
    if (fd < 0) return 0;
    wlen = 0;
    for (i = 0; i < nn && ok; i++) {
        fmt(ln, "%ld %s", notes[i].key, notes[i].t);
        ok = putln(fd, ln);
    }
    for (i = 0; i < ne && ok; i++) {
        fmt(ln, "E %ld %ld %s|%s", evs[i].s, evs[i].e, evs[i].t, evs[i].w);
        ok = putln(fd, ln);
    }
    for (i = 0; i < nct && ok; i++) {
        fmt(ln, "C %s;%s", cts[i].n, cts[i].ph);
        ok = putln(fd, ln);
    }
    ok = ok && wflush(fd);
    close(fd);
    return ok;
}

static int hasnote(long key)
{
    int i;
    for (i = 0; i < nn; i++) if (notes[i].key == key) return 1;
    return 0;
}

static int hasevent(long key)
{
    int i;
    for (i = 0; i < ne; i++) if (evs[i].s <= key && key <= evs[i].e) return 1;
    return 0;
}

/* events and notes of a day */
static int dayitems(long key, ITEM *it)
{
    int i, c = 0;
    for (i = 0; i < ne && c < PER; i++)
        if (evs[i].s <= key && key <= evs[i].e) { it[c].kind = 1; it[c].idx = i; c++; }
    for (i = 0; i < nn && c < PER; i++)
        if (notes[i].key == key) { it[c].kind = 0; it[c].idx = i; c++; }
    return c;
}

static void addday(int *y, int *m, int *d, int n)
{
    while (n > 0) {
        if (++*d > mdays(*y, *m)) { *d = 1; if (++*m > 12) { *m = 1; (*y)++; } }
        n--;
    }
    while (n < 0) {
        if (--*d < 1) { if (--*m < 1) { *m = 12; (*y)--; } *d = mdays(*y, *m); }
        n++;
    }
    if (*y < 1980) { *y = 1980; *m = 1; *d = 1; }
    if (*y > 2099) { *y = 2099; *m = 12; *d = 31; }
}

static void cleanstr(char *s)
{
    for (; *s; s++) if (*s == '|' || *s == ';') *s = ',';
}

/* guests: list "A, B, C" */
static int inwho(const char *w, const char *name)
{
    int l = strlen(name);
    const char *p = w;
    while (*p) {
        if (!strncmp(p, name, l) && (p[l] == 0 || p[l] == ',')) return 1;
        p = strchr(p, ',');
        if (!p) break;
        p++;
        while (*p == ' ') p++;
    }
    return 0;
}

static void delwho(char *w, const char *name)
{
    char out[64], *o = out;
    const char *p = w, *q;
    int l = strlen(name), n;
    *o = 0;
    while (*p) {
        q = strchr(p, ',');
        n = q ? (int)(q - p) : (int)strlen(p);
        if (!(n == l && !strncmp(p, name, l))) {
            if (o != out) { *o++ = ','; *o++ = ' '; }
            memcpy(o, p, n); o += n;
        }
        if (!q) break;
        p = q + 1;
        while (*p == ' ') p++;
    }
    *o = 0;
    strcpy(w, out);
}

static void addwho(char *w, const char *name)
{
    if (strlen(w) + strlen(name) + 3 > 60) { msgbox("Agenda", "No room for more guests"); return; }
    if (w[0]) strcat(w, ", ");
    strcat(w, name);
}

/* manage contacts; sel >= 0 in "choose" mode for an event */
static void contacts(EVENT *ev)
{
    int cur = 0, top = 0, i, rows = 13;
    unsigned k;
    char b[80], nm[30], ph[30];

    for (;;) {
        if (cur >= nct) cur = nct ? nct - 1 : 0;
        if (cur < top) top = cur;
        if (cur >= top + rows) top = cur - rows + 1;
        box(16, 3, 48, 19, H_DLG, ev ? "Event guests" : "Contacts");
        for (i = 0; i < rows; i++) {
            if (top + i < nct) {
                if (ev) fmt(b, " [%c] %-22s %s", inwho(ev->w, cts[top + i].n) ? 'x' : ' ', cts[top + i].n, cts[top + i].ph);
                else fmt(b, " %-22s %s", cts[top + i].n, cts[top + i].ph);
                vputsn(17, 5 + i, top + i == cur ? U_SEL : H_DLG, b, 46);
            } else vputsn(17, 5 + i, H_DLG, "", 46);
        }
        if (!nct) vputsn(17, 5, H_DLG, " (no contacts: press Ins to create)", 46);
        hline(17, 19, 46, H_DLG, 0xC4);
        vputsn(18, 20, H_DLG, ev ? "Enter mark/unmark  Ins new  Esc done"
                                 : "Ins new  Enter edit  Del delete  Esc exit", 44);
        k = getkey();
        if (k == K_ESC) break;
        if (k == K_UP) { if (cur) cur--; }
        else if (k == K_DOWN) { if (cur < nct - 1) cur++; }
        else if (k == K_PGUP) { cur -= rows; if (cur < 0) cur = 0; }
        else if (k == K_PGDN) { cur += rows; if (cur >= nct) cur = nct - 1; }
        else if (k == K_INS || (k == K_ENTER && !nct)) {
            if (nct >= MAXC) { msgbox("Agenda", "Contact list full"); continue; }
            nm[0] = 0; ph[0] = 0;
            cshape(1);
            if (inputbox("New contact", "Name:", nm, 22) && nm[0]) {
                inputbox("New contact", "Phone / email:", ph, 16);
                cleanstr(nm); cleanstr(ph);
                strcpy(cts[nct].n, nm); strcpy(cts[nct].ph, ph);
                cur = nct++;
                savenotes();
            }
            cshape(0);
        }
        else if (k == K_ENTER && ev) {
            if (inwho(ev->w, cts[cur].n)) delwho(ev->w, cts[cur].n); else addwho(ev->w, cts[cur].n);
            savenotes();
        }
        else if (k == K_ENTER) {
            strcpy(nm, cts[cur].n); strcpy(ph, cts[cur].ph);
            cshape(1);
            if (inputbox("Edit contact", "Name:", nm, 22) && nm[0]) {
                inputbox("Edit contact", "Phone / email:", ph, 16);
                cleanstr(nm); cleanstr(ph);
                strcpy(cts[cur].n, nm); strcpy(cts[cur].ph, ph);
                savenotes();
            }
            cshape(0);
        }
        else if (k == K_DEL && nct && !ev) {
            memmove(&cts[cur], &cts[cur + 1], (nct - cur - 1) * sizeof(CONT));
            nct--;
            savenotes();
        }
    }
}

static void agenda(void)
{
    struct dosdate_t dt;
    int y, m, d, ty, tm, td, focus = 0, ni = 0, cnt, i, first, x, yy, a, bx = 9, by = 3, run = 1;
    int ey, em, ed, nd;
    long key, tkey;
    char b[100], buf[ELEN + 2];
    unsigned k;
    ITEM it[PER];

    notes = (NOTE *)malloc(sizeof(NOTE) * MAXN);
    evs = (EVENT *)malloc(sizeof(EVENT) * MAXE);
    cts = (CONT *)malloc(sizeof(CONT) * MAXC);
    if (!notes || !evs || !cts) { msgbox("Agenda", "Out of memory"); return; }
    nn = ne = nct = 0;
    loadnotes();
    _dos_getdate(&dt);
    ty = y = dt.year; tm = m = dt.month; td = d = dt.day;
    tkey = mkkey(ty, tm, td);
    cshape(0);
    while (run) {
        key = mkkey(y, m, d);
        cnt = dayitems(key, it);
        if (ni >= cnt) ni = cnt ? cnt - 1 : 0;
        box(bx, by, 62, 18, H_DLG, "Agenda");
        /* calendar */
        i = fmt(b, "< %s %d >", mname[m - 1], y);
        vputsn(bx + 3 + (21 - i) / 2, by + 1, H_DLG, b, i);
        vputsn(bx + 3, by + 3, U_NOTE, "Mo Tu We Th Fr Sa Su", 20);
        first = dow(y, m, 1);
        for (i = 1; i <= mdays(y, m); i++) {
            long kk = mkkey(y, m, i);
            x = bx + 3 + ((first + i - 1) % 7) * 3;
            yy = by + 4 + (first + i - 1) / 7;
            a = H_DLG;
            if (hasnote(kk)) a = U_NOTE;
            if (kk == tkey) a = U_TODAY;
            if (hasevent(kk)) a = U_HOT;
            if (i == d) a = focus == 0 ? U_SEL : U_DAYF;
            fmt(b, "%2d", i);
            vputsn(x, yy, a, b, 2);
        }
        for (i = 1; i < 15; i++) vput(bx + 25, by + i, H_DLG, 0xB3);
        /* events and notes */
        fmt(b, "Day %02d/%02d/%d", d, m, y);
        vputsn(bx + 27, by + 1, U_NOTE, b, 33);
        for (i = 0; i < cnt; i++) {
            if (it[i].kind) fmt(b, "* %.29s", evs[it[i].idx].t);
            else fmt(b, "%.31s", notes[it[i].idx].t);
            vputsn(bx + 27, by + 3 + i, (focus == 1 && i == ni) ? U_SEL : (it[i].kind ? U_HOT : H_DLG), b, 33);
        }
        if (!cnt) vputsn(bx + 27, by + 3, H_DLG, "(nothing this day)", 33);
        if (focus == 1 && cnt && it[ni].kind) {
            fmt(b, "With: %.27s", evs[it[ni].idx].w[0] ? evs[it[ni].idx].w : "(no guests)");
            vputsn(bx + 27, by + 14, U_NOTE, b, 33);
        }
        hline(bx + 1, by + 15, 60, H_DLG, 0xC4);
        vputsn(bx + 2, by + 16, H_DLG, focus ? "Enter edit  Del delete  A guests  Tab back"
                                             : "Enter note  E event  C contacts  Tab list  T today", 58);
        k = getkey();
        if (focus == 0) {
            if (k == K_ESC) run = 0;
            else if (k == K_LEFT) addday(&y, &m, &d, -1);
            else if (k == K_RIGHT) addday(&y, &m, &d, 1);
            else if (k == K_UP) addday(&y, &m, &d, -7);
            else if (k == K_DOWN) addday(&y, &m, &d, 7);
            else if (k == K_PGUP || k == K_PGDN || k == K_CPGUP || k == K_CPGDN) {
                if (k == K_PGUP) { if (--m < 1) { m = 12; y--; } }
                else if (k == K_PGDN) { if (++m > 12) { m = 1; y++; } }
                else y += (k == K_CPGUP) ? -1 : 1;
                if (y < 1980) y = 1980;
                if (y > 2099) y = 2099;
                if (d > mdays(y, m)) d = mdays(y, m);
            }
            else if (k == K_HOME || toupper(k & 0xFF) == 'T') { y = ty; m = tm; d = td; }
            else if (k == K_TAB) { if (cnt) { focus = 1; ni = 0; } }
            else if (toupper(k & 0xFF) == 'C') contacts(NULL);
            else if (toupper(k & 0xFF) == 'E') {
                if (ne >= MAXE) msgbox("Agenda", "Too many events");
                else {
                    buf[0] = 0;
                    fmt(b, "Event starting on %02d/%02d/%d:", d, m, y);
                    cshape(1);
                    if (inputbox("New event", b, buf, ELEN) && buf[0]) {
                        strcpy(b, "1");
                        inputbox("New event", "How many days (from that day)?", b, 3);
                        nd = atoi(b);
                        if (nd < 1) nd = 1;
                        if (nd > 99) nd = 99;
                        ey = y; em = m; ed = d;
                        addday(&ey, &em, &ed, nd - 1);
                        cleanstr(buf);
                        evs[ne].s = key;
                        evs[ne].e = mkkey(ey, em, ed);
                        strcpy(evs[ne].t, buf);
                        evs[ne].w[0] = 0;
                        ne++;
                        if (!savenotes()) msgbox("Error", "Cannot save AGENDA.TXT");
                    }
                    cshape(0);
                }
            }
            else if (k == K_ENTER || k == K_INS || toupper(k & 0xFF) == 'N') {
                if (nn >= MAXN) msgbox("Agenda", "Agenda full");
                else if (cnt >= PER) msgbox("Agenda", "Too many items that day");
                else {
                    buf[0] = 0;
                    fmt(b, "Note for %02d/%02d/%d:", d, m, y);
                    cshape(1);
                    if (inputbox("New note", b, buf, ELEN) && buf[0]) {
                        cleanstr(buf);
                        notes[nn].key = key;
                        strcpy(notes[nn].t, buf);
                        nn++;
                        if (!savenotes()) msgbox("Error", "Cannot save AGENDA.TXT");
                    }
                    cshape(0);
                }
            }
        } else {
            if (k == K_ESC || k == K_TAB) focus = 0;
            else if (k == K_UP) { if (ni) ni--; }
            else if (k == K_DOWN) { if (ni < cnt - 1) ni++; }
            else if (toupper(k & 0xFF) == 'A' || k == K_INS) {
                if (it[ni].kind) {
                    if (!nct) msgbox("Agenda", "No contacts: press C in the calendar");
                    else contacts(&evs[it[ni].idx]);
                }
            }
            else if (k == K_DEL) {
                i = it[ni].idx;
                if (it[ni].kind) {
                    if (askkey("Agenda", "Delete the event (all its days)?") == 'Y') {
                        memmove(&evs[i], &evs[i + 1], (ne - i - 1) * sizeof(EVENT));
                        ne--;
                        savenotes();
                    }
                } else {
                    memmove(&notes[i], &notes[i + 1], (nn - i - 1) * sizeof(NOTE));
                    nn--;
                    savenotes();
                }
                if (!dayitems(key, it)) focus = 0;
            }
            else if (k == K_ENTER) {
                i = it[ni].idx;
                strcpy(buf, it[ni].kind ? evs[i].t : notes[i].t);
                cshape(1);
                if (inputbox(it[ni].kind ? "Edit event" : "Edit note", "Text:", buf, ELEN) && buf[0]) {
                    cleanstr(buf);
                    strcpy(it[ni].kind ? evs[i].t : notes[i].t, buf);
                    savenotes();
                }
                cshape(0);
            }
        }
    }
    free(notes); free(evs); free(cts);
}

/* ======================= ASCII TABLE ======================= */
static void asciitab(void)
{
    int cur = 65, r, c, i, x = 11, y = 1, ch;
    unsigned k;
    char b[80], bin[9];

    cshape(0);
    for (;;) {
        box(x, y, 58, 22, H_DLG, "ASCII table");
        for (i = 0; i < 16; i++) {
            fmt(b, "%X", i);
            vputsn(x + 5 + i * 3, y + 1, U_HOT, b, 1);
            vputsn(x + 2, y + 2 + i, U_HOT, b, 1);
        }
        for (r = 0; r < 16; r++)
            for (c = 0; c < 16; c++) {
                ch = r * 16 + c;
                vput(x + 4 + c * 3, y + 2 + r, ch == cur ? U_SEL : H_DLG, ' ');
                vput(x + 5 + c * 3, y + 2 + r, ch == cur ? U_SEL : H_DLG, ch);
                vput(x + 6 + c * 3, y + 2 + r, ch == cur ? U_SEL : H_DLG, ' ');
            }
        for (i = 0; i < 8; i++) bin[i] = (cur & (0x80 >> i)) ? '1' : '0';
        bin[8] = 0;
        hline(x + 1, y + 18, 56, H_DLG, 0xC4);
        fmt(b, " Decimal %3d   Hex %02X   Binary %s", cur, cur, bin);
        vputsn(x + 2, y + 19, H_DLG, b, 54);
        vputsn(x + 2, y + 20, H_DLG, "Arrows move   Type a key = go to it   Esc exit", 54);
        k = getkey();
        ch = k & 0xFF;
        if (k == K_ESC || k == K_ENTER) break;
        if (k == K_LEFT) cur = (cur + 255) & 255;
        else if (k == K_RIGHT) cur = (cur + 1) & 255;
        else if (k == K_UP) cur = (cur + 240) & 255;
        else if (k == K_DOWN) cur = (cur + 16) & 255;
        else if (k == K_HOME) cur = 0;
        else if (k == K_END) cur = 255;
        else if (k == K_PGUP) cur = (cur + 192) & 255;
        else if (k == K_PGDN) cur = (cur + 64) & 255;
        else if (ch >= 32) cur = ch;
    }
}

/* ======================= COMPARE FILES ======================= */
#define MAXL   600
#define FBSZ   14000U
#define WIN    60

typedef struct { unsigned char t; int a, b; } ROW;   /* t: 0 same, 1 only in A, 2 only in B, 3 changed */

static char *fb[2];
static unsigned *lo[2], *le[2], *lh[2];
static int nl[2];
static ROW *rows;
static int nrows;
static int *ds, nds;
static int trunc_;

static int loadf(int n, const char *name)
{
    int fd;
    unsigned got, tot = 0, s, i, e, e2, lim;
    unsigned h, mx;

    fd = open(name, O_RDONLY | O_BINARY);
    if (fd < 0) return 0;
    {
        long sz = filelength(fd);
        unsigned cap = sz > (long)FBSZ ? FBSZ : (unsigned)sz;
        fb[n] = (char *)malloc(cap + 2);
        if (!fb[n]) { close(fd); return -1; }
        lim = cap;
        if (sz > (long)FBSZ) trunc_ = 1;
    }
    while (tot < lim) {
        unsigned want = lim - tot > 16384U ? 16384U : lim - tot;
        if (_dos_read(fd, (void __far *)(fb[n] + tot), want, &got) || !got) break;
        tot += got;
    }
    close(fd);
    /* a line takes at least 1 byte: no need for more tables than possible lines */
    mx = tot / 1 + 1 > MAXL ? MAXL : tot + 1;
    lo[n] = (unsigned *)malloc(mx * 2);
    le[n] = (unsigned *)malloc(mx * 2);
    lh[n] = (unsigned *)malloc(mx * 2);
    if (!lo[n] || !le[n] || !lh[n]) return -1;
    nl[n] = 0;
    s = 0;
    for (i = 0; i <= tot && nl[n] < (int)mx; i++) {
        if (i == tot || fb[n][i] == '\n') {
            if (i == tot && s == tot) break;
            e = i;
            e2 = e;
            while (e2 > s && (fb[n][e2 - 1] == '\r' || fb[n][e2 - 1] == ' ' || fb[n][e2 - 1] == '\t' || fb[n][e2 - 1] == 26)) e2--;
            h = 0;
            { unsigned q; for (q = s; q < e2; q++) h = h * 31 + (unsigned char)fb[n][q]; }
            lo[n][nl[n]] = s; le[n][nl[n]] = e2; lh[n][nl[n]] = h;
            nl[n]++;
            s = i + 1;
        }
    }
    if (nl[n] >= MAXL) trunc_ = 1;
    return 1;
}

static int eq(int i, int j)
{
    unsigned la = le[0][i] - lo[0][i];
    if (lh[0][i] != lh[1][j] || la != le[1][j] - lo[1][j]) return 0;
    return memcmp(fb[0] + lo[0][i], fb[1] + lo[1][j], la) == 0;
}

static void addrow(int t, int a, int b)
{
    rows[nrows].t = (unsigned char)t;
    rows[nrows].a = a;
    rows[nrows].b = b;
    nrows++;
}

static void dodiff(void)
{
    int i = 0, j = 0, k, k1, k2, prev = 0;
    nrows = 0;
    while (i < nl[0] || j < nl[1]) {
        if (i >= nl[0]) { addrow(2, -1, j++); continue; }
        if (j >= nl[1]) { addrow(1, i++, -1); continue; }
        if (eq(i, j)) { addrow(0, i++, j++); continue; }
        k1 = k2 = 0;
        for (k = 1; k <= WIN; k++) {
            if (i + k < nl[0] && eq(i + k, j)) { k1 = k; break; }
            if (j + k < nl[1] && eq(i, j + k)) { k2 = k; break; }
        }
        if (k1) { while (k1--) addrow(1, i++, -1); }
        else if (k2) { while (k2--) addrow(2, -1, j++); }
        else addrow(3, i++, j++);
    }
    nds = 0;
    for (i = 0; i < nrows; i++) {
        if (rows[i].t && !prev && nds < 600) ds[nds++] = i;
        prev = rows[i].t != 0;
    }
}

static void putline(int x, int y, int a, int n, int li, int w, int hs, int h0, int h1)
{
    unsigned o, l;
    int i, c, at;
    unsigned short __far *p = vid + y * 80 + x;
    vdirty = 1;
    if (li >= 0) { o = lo[n][li]; l = le[n][li] - o; }
    else { o = 0; l = 0; }
    for (i = 0; i < w; i++) {
        if ((unsigned)(i + hs) < l) {
            c = (unsigned char)fb[n][o + i + hs];
            if (c < 32) c = ' ';
        } else c = ' ';
        at = (i + hs >= h0 && i + hs < h1) ? U_CHGHI : a;
        *p++ = ((unsigned)col[at] << 8) | (unsigned char)c;
    }
}

/* different part of two lines: between the equal prefix and suffix */
static void chgrange(int i, int j, int *a0, int *a1, int *b0, int *b1)
{
    unsigned la = le[0][i] - lo[0][i], lb = le[1][j] - lo[1][j], p = 0, s = 0;
    const char *x = fb[0] + lo[0][i], *y = fb[1] + lo[1][j];
    while (p < la && p < lb && x[p] == y[p]) p++;
    while (s < la - p && s < lb - p && x[la - 1 - s] == y[lb - 1 - s]) s++;
    *a0 = p; *a1 = la - s;
    *b0 = p; *b1 = lb - s;
}

static void difview(const char *na, const char *nb)
{
    int top = 0, hs = 0, r, ri, la, lb, aa, ab, h = 22, i, cur, h0, h1, h2, h3;
    unsigned k;
    char b[90];
    static const char *kl[10] = { "", "", "Quit", "", "", "", "NxtDif", "PrvDif", "", "Quit" };

    cshape(0);
    for (;;) {
        /* titles */
        vputsn(0, 0, U_HDR, "", 80);
        vputsn(1, 0, U_HDR, na, 37);
        vputsn(41, 0, U_HDR, nb, 38);
        vput(39, 0, U_HDR, 0xB3);
        for (r = 0; r < h; r++) {
            ri = top + r;
            vput(39, 1 + r, U_SEP, 0xB3);
            if (ri >= nrows) {
                hline(0, 1 + r, 39, U_TXT, ' ');
                hline(40, 1 + r, 40, U_TXT, ' ');
                continue;
            }
            la = rows[ri].a; lb = rows[ri].b;
            aa = ab = U_TXT;
            if (rows[ri].t == 1) aa = U_DEL;
            else if (rows[ri].t == 2) ab = U_INS;
            else if (rows[ri].t == 3) aa = ab = U_CHG;
            h0 = h1 = h2 = h3 = 0;
            if (rows[ri].t == 3) chgrange(la, lb, &h0, &h1, &h2, &h3);
            putline(0, 1 + r, aa, 0, la, 39, hs, h0, h1);
            putline(40, 1 + r, ab, 1, lb, 40, hs, h2, h3);
        }
        /* status */
        cur = 0;
        for (i = 0; i < nds; i++) if (ds[i] <= top + 2) cur = i + 1;
        if (!nds) fmt(b, " The files are the same");
        else fmt(b, " Difference %d of %d     Column %d%s", cur ? cur : 1, nds, hs + 1, trunc_ ? "     (very big files: only the start is compared)" : "");
        vputsn(0, 23, U_HDR, b, 80);
        for (i = 0; i < 10; i++) {
            fmt(b, "%2d", i + 1);
            vputsn(i * 8, 24, U_KEYN, b, 2);
            vputsn(i * 8 + 2, 24, U_KEYL, kl[i], 6);
        }
        k = getkey();
        if (k == K_ESC || k == K_F3 || k == K_F10) break;
        if (k == K_UP) { if (top) top--; }
        else if (k == K_DOWN) { if (top + h < nrows) top++; }
        else if (k == K_PGUP) { top -= h - 1; if (top < 0) top = 0; }
        else if (k == K_PGDN) { if (top + h < nrows) top += h - 1; if (top + h > nrows && nrows > h) top = nrows - h; }
        else if (k == K_HOME) { top = 0; hs = 0; }
        else if (k == K_END) { top = nrows > h ? nrows - h : 0; }
        else if (k == K_LEFT) { hs -= 8; if (hs < 0) hs = 0; }
        else if (k == K_RIGHT) { if (hs < 200) hs += 8; }
        else if (k == K_F7 || toupper(k & 0xFF) == 'N') {
            for (i = 0; i < nds; i++) if (ds[i] > top + 2) { top = ds[i] - 2; break; }
            if (top < 0) top = 0;
        }
        else if (k == K_F8 || toupper(k & 0xFF) == 'P') {
            for (i = nds - 1; i >= 0; i--) if (ds[i] < top + 2) { top = ds[i] - 2; break; }
            if (top < 0) top = 0;
        }
    }
}

static int diffmain(const char *a, const char *b)
{
    int ra, rb;
    rows = NULL;
    ra = loadf(0, a);
    rb = ra > 0 ? loadf(1, b) : 1;
    if (ra <= 0 || rb <= 0) {
        msgbox("Compare", ra == 0 ? "Cannot open the first file" :
                           ra < 0 ? "Out of memory (first file)" :
                           rb == 0 ? "Cannot open the second file" : "Out of memory (second file)");
        return 1;
    }
    rows = (ROW *)malloc((nl[0] + nl[1] + 2) * sizeof(ROW));
    ds = (int *)malloc(600 * sizeof(int));
    if (!rows || !ds) { msgbox("Compare", "Out of memory"); return 1; }
    dodiff();
    difview(a, b);
    return 0;
}

/* ======================= main ======================= */
int main(int argc, char **argv)
{
    char *bs;
    int rc = 0;

    if (argc < 2) {
        write(1, "UTILS -agenda | -ascii | -diff file1 file2\r\n", 44);
        return 1;
    }
    strncpy(udir, argv[0], 79);
    udir[79] = 0;
    bs = strrchr(udir, '\\');
    if (!bs) bs = strchr(udir, ':');
    if (bs) bs[1] = 0; else udir[0] = 0;

    vinit();
    cshape(0);
    if (!stricmp(argv[1], "-agenda")) agenda();
    else if (!stricmp(argv[1], "-ascii")) asciitab();
    else if (!stricmp(argv[1], "-diff") && argc >= 4) rc = diffmain(argv[2], argv[3]);
    vend();
    return rc;
}
