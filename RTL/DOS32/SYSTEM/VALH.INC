{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

procedure Val( const S: String; var L: LongInt; var Code: Integer);
procedure Val( const S: String; var L: LongInt);
procedure Val( const S: String; var I: Integer; var Code: Integer);
procedure Val( const S: String; var I: Integer);
procedure Val( const S: String; var SI: ShortInt; var Code: Integer);
procedure Val( const S: String; var SI: ShortInt);
procedure Val( const S: String; var DW: DWord; var Code: Integer);
procedure Val( const S: String; var DW: DWord);
procedure Val( const S: String; var W: Word; var Code: Integer);
procedure Val( const S: String; var W: Word);
procedure Val( const S: String; var B: Byte; var Code: Integer);
procedure Val( const S: String; var B: Byte);

procedure Val( const S: String; var E: Extended; var Code: Integer);
procedure Val( const S: String; var E: Extended);
procedure Val( const S: String; var D: Double; var Code: Integer);
procedure Val( const S: String; var D: Double);
procedure Val( const S: String; var Sn: Single; var Code: Integer);
procedure Val( const S: String; var Sn: Single);