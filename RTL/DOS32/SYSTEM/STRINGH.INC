
{ Средства для работы со строками }

operator +=(var a: String; const b: String) res: String;
procedure Insert( const SubStr: String; var S: String; Pos: Integer);
function Copy( const S: String; Pos, Len: Integer): String;

procedure Delete( var S: String; Pos, Num: Byte);
function Pos( const SubStr, S: String): LongInt;
