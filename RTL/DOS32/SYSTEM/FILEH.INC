
{ Средства для работы с двоичными файлами }

type

  FileRec = record
              Handle: Word;
              Mode: Word;
              RecSize: LongInt;
              _Private: array[1..24] of Byte;
              UserData: array[1..16] of Byte;
              Name: array[0..79] of Char;
            end;

const
  FileMode: LongInt = 2;

{ Типизированные файлы }

procedure ReSet( var F: TypedFile);
procedure ReWrite( var F: TypedFile);

procedure Close( var F: TypedFile);

function EOF( var F: TypedFile): Boolean;
procedure Erase( var F: TypedFile);
procedure ReName( var F: TypedFile; const NewName: String);

procedure Seek( var F: TypedFile; NewPos: LongInt);
function FilePos( var F: TypedFile): LongInt;
function FileSize( var F: TypedFile): LongInt;
procedure Truncate( var F: TypedFile);

{ Нетипизированные файлы }

procedure ReSet( var F: File);
procedure ReSet( var F: File; RecSize: LongInt);
procedure ReWrite( var F: File);
procedure ReWrite( var F: File; RecSize: LongInt);

procedure Close( var F: File);

procedure BlockRead( var F: File; var Buf; Count: LongInt; var Result: LongInt);
procedure BlockRead( var F: File; var Buf; Count: LongInt);

procedure BlockWrite( var F: File; var Buf; Count: LongInt; var Result: LongInt);
procedure BlockWrite( var F: File; var Buf; Count: LongInt);

function EOF( var F: File): Boolean;
procedure Erase( var F: File);
procedure ReName( var F: File; const NewName: String);

procedure Seek( var F: file; NewPos: LongInt);
function FilePos( var F: file): LongInt;
function FileSize( var F: file): LongInt;
procedure Truncate( var F: file);
