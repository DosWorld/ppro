
const

  fmClosed   = $D7B0;
  fmInput    = $D7B1;
  fmOutput   = $D7B2;
  fmInOut    = $D7B3;
  fmAppend   = $D7B4;

  NameLength = 79;

type

  TextBuf = array[0..127] of Char;

  TextRec = record
     Handle : Word;
     Mode : Word;
     BufSize : LongInt;
     BufPos : Word;
     BufEnd : Word;
     BufPtr : ^TextBuf;
     OpenFunc : Pointer;
     InOutFunc : Pointer;
     FlushFunc : Pointer;
     CloseFunc : Pointer;
     UserData : array[1..16] of Byte;
     Name : array [0..NameLength] of Char;
     Buffer : TextBuf;
  end;


procedure Reset( var TextFile: Text);
procedure ReWrite( var TextFile: Text);
procedure Close( var TextFile: Text);
procedure Append( var TextFile: Text);
procedure Flush( var TextFile: Text);

function EOF( var TextFile: Text): Boolean;
function EOLn( var TextFile: Text): Boolean;
function SeekEOF( var TextFile: Text): Boolean;
function SeekEOLn( var TextFile: Text): Boolean;

procedure ReName( var TextFile: Text; const NewName: String);
procedure Erase( var TextFile: Text);

procedure SetTextBuf( var TextFile: Text; var Buffer; Size: LongInt);
