@echo off
md OUT
md OUT\XT
md OUT\AT
wcl -ms -0 -os -k4096 -fe=OUT\XT\nc.exe nc.c
wcl -ms -0 -os -k8192 -fe=OUT\XT\utils.exe utils.c
wcl -ms -0 -os -k12288 -fe=OUT\XT\cells.exe cells.c
wcl -ms -2 -oneatx -os -k4096 -d_X286 -fe=OUT\AT\nc.exe nc.c
wcl -ms -2 -oneatx -k8192 -fe=OUT\AT\utils.exe utils.c
wcl -ms -2 -oneatx -k12288 -fe=OUT\AT\cells.exe cells.c
wasm -q ncl.asm
wlink format dos com file ncl.obj name OUT\XT\nc.com option quiet
copy OUT\XT\nc.com OUT\AT\nc.com
copy NC.EXT OUT\XT
copy NC.EXT OUT\AT
del *.obj
