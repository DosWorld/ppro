{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{         UnitStrm unit                                                 }
{                                              (c) Copyright 1997-1999  }
{                                   Iggor Khachko - hachko@icl.kazan.su }
{-----------------------------------------------------------------------}

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

unit UnitStrm;

interface

uses Objects, FileColl;

type
  tCRC = array [0..15] of Byte;

{$IFDEF TP}
  tSize = Word;
{$ENDIF}

  pUnitStream = ^tUnitStream;
  tUnitStream = object( tBufStream)
    CRC: tCRC;
    CrcPos: Byte;
    WriteHeader: Boolean;
    FileName: String;
    constructor Init( aFileName: String; aMode: Integer);
    destructor Done; virtual;
    procedure WriteByte( Val: Byte);
    procedure WriteInt( Val: Integer);
    procedure WriteLong( Val: LongInt);
    function ReadByte: Byte;
    function ReadInt: Integer;
    function ReadLong: LongInt;
    procedure CheckHeader;
    procedure Write( var Buf; Count: tSize); virtual;
  end;

const
  UnitHeaderStr = 'Pascal Pro Unit.'#26;

type
  tMagicHeader = array [0..Length( UnitHeaderStr)-1] of char;

const
  UnitHeader: tMagicHeader = UnitHeaderStr;

type
  tUnitHeader = record
    MagicHeader: tMagicHeader;
    Version: Word;
    Res: array [ SizeOf( tMagicHeader)+SizeOf( Word)..31] of Byte;
    CRC: tCRC;
  end;

implementation

uses Errors, Symbols, PasComp, Compiler;

{ tUnitStream }
constructor tUnitStream.Init( aFileName: String; aMode: Integer);
  begin
    inherited Init( aFileName, aMode, 4096);
    FileName := aFileName;
    WriteHeader := False;
    if Status <> stOK then
      with CurCompiler^ do
        Error( erFileAccessDenied, Files^.PrevLine, Files^.PrevCol, FileName);
    case aMode of
      stOpenRead:
        CheckHeader;
      stOpenWrite,
      stCreate:
        begin
          WriteHeader := True;
          Seek( SizeOf( tUnitHeader));
        end;
    end;
  end;

destructor tUnitStream.Done;
  var
    Header: tUnitHeader;
  begin
    if WriteHeader then
      begin
        Header.MagicHeader := UnitHeader;
        Header.CRC := CRC;
        Seek( 0);
        inherited Write( Header, SizeOf( Header));
      end;
    inherited Done;
  end;

procedure tUnitStream.WriteByte( Val: Byte);
  begin
    Write( Val, SizeOf( Val));
  end;

procedure tUnitStream.WriteInt( Val: Integer);
  begin
    Write( Val, SizeOf( Val));
  end;

procedure tUnitStream.WriteLong( Val: LongInt);
  begin
    Write( Val, SizeOf( Val));
  end;

function tUnitStream.ReadByte: Byte;
{$IFNDEF PPRO}
  var
    Res: Byte;
  begin
    Read( Res, SizeOf( Res));
    ReadByte := Res;
  end;
{$ELSE}
  begin
    Read( Result, SizeOf( Result));
  end;
{$ENDIF}

function tUnitStream.ReadInt: Integer;
{$IFNDEF PPRO}
  var
    Res: Integer;
  begin
    Read( Res, SizeOf( Res));
    ReadInt := Res;
  end;
{$ELSE}
  begin
    Read( Result, SizeOf( Result));
  end;
{$ENDIF}

function tUnitStream.ReadLong: LongInt;
{$IFNDEF PPRO}
  var
    Res: LongInt;
  begin
    Read( Res, SizeOf( Res));
    ReadLong := Res;
  end;
{$ELSE}
  begin
    Read( Result, SizeOf( Result));
  end;
{$ENDIF}

procedure tUnitStream.CheckHeader;
  var
    Header: tUnitHeader;
  begin
    inherited Read( Header, SizeOf( Header));
    if (Status <> stOK) or (Header.MagicHeader <> UnitHeader) then
      with CurCompiler^ do
        Error( erUnitFileFormatError, Files^.PrevLine, Files^.PrevCol, FileName);
  end;


procedure tUnitStream.Write( var Buf; Count: tSize);
  var
    B: tByteArray absolute Buf;
    I: tSize;
  begin
    for I := 0 to Count - 1 do
      begin
        CRC[ CrcPos] := CRC[ CrcPos] xor B[ I];
        CrcPos := (CrcPos + 1) and $0F;
      end;
    inherited Write( Buf, Count);
  end;


end.