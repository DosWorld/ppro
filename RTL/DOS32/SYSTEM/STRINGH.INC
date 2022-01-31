{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

operator +=(var a: String; const b: String) res: String;
procedure Insert( const SubStr: String; var S: String; Pos: Integer);
function Copy( const S: String; Pos, Len: Integer): String;
procedure Delete( var S: String; Pos, Num: Byte);
function Pos( const SubStr, S: String): LongInt;