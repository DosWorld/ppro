{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

const

  HeapOrg: Pointer = nil;
  HeapEnd: Pointer = nil;
  HeapPtr: Pointer = nil;
  FreeList: Pointer = nil;
  HeapError: Pointer = nil;
  HeapHandle: LongInt = 0;

  HeapSizeLo = 0;
  HeapSizeHi = 1024 * 1024 * 4 shr 16;

procedure GetMem( var P: Pointer; Size: LongInt);
procedure FreeMem( var P: Pointer; Size: LongInt);

function MemAvail: LongInt;
function MaxAvail: LongInt;
