
        .8086
_TEXT   segment word public 'CODE'
        assume  cs:_TEXT, ds:_TEXT, es:_TEXT, ss:_TEXT
        org     100h

start:  jmp     init

        even

shared:
sig     db      'NCL1'
run     db      0
err     db      0
have    db      0
        db      0
prog    db      80 dup (0)
tail    db      128 dup (0)
state   db      256 dup (0)

ncpath  db      80 dup (0)
nctail  db      13, ' /L:'
nctseg  db      'SSSS:OOOO', 13
pblock  dw      0
        dw      0, 0
        dw      5Ch, 0
        dw      6Ch, 0
savesp  dw      0
savess  dw      0
msgnonc db      'NC: cannot find NC.EXE', 13, 10, '$'

again:
        mov     dx, offset ncpath
        mov     word ptr pblock+2, offset nctail
        call    doexec
        jc      nonc
        cmp     run, 1
        jne     fin
        mov     run, 0

        push    ds
        pop     es
        mov     si, offset tail+1
        mov     di, 5Ch
        mov     ax, 2901h
        int     21h
        mov     di, 6Ch
        mov     ax, 2901h
        int     21h
        mov     dx, offset prog
        mov     word ptr pblock+2, offset tail
        call    doexec
        mov     err, 0
        jnc     again
        mov     err, al
        jmp     again
nonc:
        mov     dx, offset msgnonc
        mov     ah, 9
        int     21h
fin:
        mov     ax, 4C00h
        int     21h

doexec:
        push    ds
        push    es
        push    bp
        mov     cs:savesp, sp
        mov     cs:savess, ss
        push    cs
        pop     es
        mov     bx, offset pblock
        mov     ax, 4B00h
        int     21h
        cli
        mov     ss, cs:savess
        mov     sp, cs:savesp
        sti
        pop     bp
        pop     es
        pop     ds
        ret

doshrink:
        mov     bx, offset endres
        add     bx, 15
        mov     cl, 4
        shr     bx, cl
        mov     ah, 4Ah
        int     21h
        jmp     again

        even
pad     db      64 dup (0)
stk     db      768 dup (0)
stktop  label   word
endres  label   byte

init:
        cld
        mov     sp, offset stktop

        mov     es, ds:[2Ch]
        xor     di, di
        xor     al, al
        mov     cx, 0FFFFh
skipenv:
        repne   scasb
        cmp     es:[di], al
        jne     skipenv
        lea     si, [di+3]
        mov     di, offset ncpath
        mov     bx, di
cpath:
        mov     al, es:[si]
        inc     si
        mov     [di], al
        inc     di
        cmp     al, '\'
        jne     cpath1
        mov     bx, di
cpath1:
        or      al, al
        jnz     cpath

        pushf
        pop     ax
        and     ax, 0FFFh
        push    ax
        popf
        pushf
        pop     ax
        and     ax, 0F000h
        mov     si, offset n286
        cmp     ax, 0F000h
        jne     cpuok
        mov     si, offset n86
cpuok:
        push    ds
        pop     es
        mov     di, bx
cname:
        lodsb
        stosb
        or      al, al
        jnz     cname

        mov     di, offset nctseg
        mov     ax, cs
        call    hex4
        inc     di
        mov     ax, offset shared
        call    hex4

        mov     word ptr pblock+4, cs
        mov     word ptr pblock+8, cs
        mov     word ptr pblock+12, cs
        jmp     doshrink

hex4:
        mov     cx, 4
hex4a:
        push    cx
        mov     cl, 4
        rol     ax, cl
        mov     bx, ax
        and     bx, 0Fh
        mov     dl, hexdig[bx]
        mov     [di], dl
        inc     di
        pop     cx
        loop    hex4a
        ret

hexdig  db      '0123456789ABCDEF'
n86     db      'NC.EXE', 0
n286    db      'NC.EXE', 0

_TEXT   ends
        end     start
