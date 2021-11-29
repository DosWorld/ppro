
{ Утилиты для работы с динамической памятью }

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

