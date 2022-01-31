{                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/gpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

unit Profile;

interface

uses Objects;

function GetPrivateProfileString( const FileName: String; const Section: String;
    const Key: String): String;

function SectionExists( const FileName: String; const Section: String): Boolean;

type

{$IFNDEF PPRO}
  tIndex = Integer;
{$ENDIF}  

  pKeyItem = ^tKeyItem;
  tKeyItem = object( tObject)
    Name: pString;
    Value: pString;

    constructor Create( const aName, aValue: String);
    destructor Done; virtual;

    function GetName: String;
    function GetValue: String;
  end;

  pKeyCollection = ^tKeyCollection;
  tKeyCollection = object( tStringCollection)
    procedure FreeItem( Item: Pointer); virtual;
    function KeyOf( Item: Pointer): Pointer; virtual;
    function GetValue( const Key: String): String;
  end;

function ReadSection( const FileName: String;
    const Section: String): pKeyCollection;

type

  tLineType = ( cltUnknown, cltSectionDeclaration, cltKeyItem);

  pProfileScanner = ^tProfileScanner;
  tProfileScanner = object( tObject)
    Stream: pStream;
    LastChar: Char;
    CurrentSection: String;
    Name: String;
    Value: String;
    CurrentLine: tLineType;
    constructor Create( const aFileName: String);
    destructor Done; virtual;
    procedure ReadLine;
    function ReadChar: Char;
    function ReadName: String;
    function ReadValue: String;
    procedure SkipSpaces;
    procedure SkipLine;
    function Search( const Section: String; const Key: String): Boolean;
  end;

implementation


constructor tKeyItem.Create( const aName, aValue: String);
  begin
    inherited Init;
    Name := NewStr( aName);
    Value := NewStr( aValue);
  end;

destructor tKeyItem.Done;
  begin
    if Assigned( Name) then
      DisposeStr( Name);
    if Assigned( Value) then
      DisposeStr( Value);
    inherited Done;
  end;

function tKeyItem.GetName: String;
  begin
    if Assigned( Name) then
      GetName := Name^
    else
      GetName := '';
  end;

function tKeyItem.GetValue: String;
  begin
    if Assigned( Value) then
      GetValue := Value^
    else
      GetValue := '';
  end;


{--- tKeyCollection ---}
procedure tKeyCollection.FreeItem( Item: Pointer);
  begin
    Dispose( pKeyItem( Item), Done);
  end;

function tKeyCollection.KeyOf( Item: Pointer): Pointer;
  begin
    KeyOf := pKeyItem( Item)^.Name;
{writeln( pkeyitem( item)^.getname);}
  end;

function tKeyCollection.GetValue( const Key: String): String;
  var
    I: tIndex;
    P: pKeyItem;
  begin
    GetValue := '';
{writeln( 'searching ', key);}
    if Search( @Key, I) then
      begin
        P := At( I);
{writeln( p^.getvalue);}
        GetValue := P^.GetValue;
      end;
  end;


{--- tProfileScanner ---}
constructor tProfileScanner.Create( const aFileName: String);
  begin
    inherited Init;
    Stream := New( pDosStream, Init( aFileName, stOpenRead));
    LastChar := #0;
    ReadChar;
    CurrentLine := cltUnknown;
  end;

destructor tProfileScanner.Done;
  begin
    if Assigned( Stream) then
      Dispose( Stream, Done);
    inherited Done;
  end;

procedure tProfileScanner.ReadLine;
  begin
    while True do
      begin
        SkipSpaces;
        if LastChar <> ';' then break;
        SkipLine;
      end;
    case LastChar of
      '[':
        begin
          ReadChar;
          SkipSpaces;
          Name := '';
          Value := '';
          CurrentSection := ReadName;
          SkipLine;
          CurrentLine := cltSectionDeclaration;
        end;
      '_', 'A'..'Z', 'a'..'z', '0'..'9':
        begin
          Name := ReadName;
          SkipSpaces;
          Value := '';
          if LastChar = '=' then
            begin
              ReadChar;
              SkipSpaces;
              if LastChar = '''' then
                Value := ReadValue;
            end;
          CurrentLine := cltKeyItem;
          SkipLine;
        end;
      else
        CurrentLine := cltUnknown;
    end;
  end;

function tProfileScanner.ReadChar: Char;
  begin
    Stream^.Read( LastChar, SizeOf( Char));
    if Stream^.Status <> stOk then
      LastChar := #26;
    ReadChar := LastChar;
  end;

procedure tProfileScanner.SkipSpaces;
  begin
    while LastChar in [ ' ', #9, #13, #10] do
      ReadChar;
  end;

procedure tProfileScanner.SkipLine;
  begin
    while LastChar <> #13 do
      if ReadChar = #26 then Exit;
    if ReadChar = #10 then ReadChar;
  end;

function tProfileScanner.ReadName: String;
  var
    Res: String;
  begin
    Res := '';
    while LastChar in [ '_', 'A'..'Z', 'a'..'z', '0'..'9'] do
      begin
        Res := Res + LastChar;
        ReadChar;
      end;
    ReadName := Res;
  end;

function tProfileScanner.ReadValue: String;
  var
    Res: String;
  begin
    Res := '';
    if LastChar = '''' then ReadChar;
    while not (LastChar in [ '''', #13, #26]) do
      begin
        Res := Res + LastChar;
        ReadChar;
      end;
    if LastChar = '''' then ReadChar;
    ReadValue := Res;
  end;

function tProfileScanner.Search( const Section: String; const Key: String): Boolean;
  begin
    Search := False;
    while Section <> CurrentSection do
      begin
        ReadLine;
        while CurrentLine = cltKeyItem do
          ReadLine;
        if LastChar = #26 then break;
      end;
    if Section = CurrentSection then
      begin
        if CurrentLine = cltSectionDeclaration then
          ReadLine;
        if Key = '' then
          begin
            Search := True;
            Exit;
          end;
        while CurrentLine = cltKeyItem do
          begin
            if Name = Key then
              begin
                Search := True;
                Exit;
              end;
            ReadLine;
            if LastChar = #26 then
              break;
          end;
      end;
  end;


function GetPrivateProfileString( const FileName: String; const Section: String;
    const Key: String): String;
  var
    Profiler: pProfileScanner;
  begin
    Profiler := New( pProfileScanner, Create( FileName));
    if not Profiler^.Search( Section, Key) then
      GetPrivateProfileString := ''
    else
      GetPrivateProfileString := Profiler^.Value;
    Dispose( Profiler, Done);
  end;


function ReadSection( const FileName: String;
    const Section: String): pKeyCollection;
  var
    Profiler: pProfileScanner;
    Res: pKeyCollection;
  begin
    Profiler := New( pProfileScanner, Create( FileName));
    if not Profiler^.Search( Section, '') then
      Res := nil
    else
      begin
        Res := New( pKeyCollection, Init( 4, 4));
        while Profiler^.CurrentLine = cltKeyItem do
          begin
            Res^.Insert( New( pKeyItem,
              Create( Profiler^.Name, Profiler^.Value)));
            Profiler^.ReadLine;
          end;
      end;
    Dispose( Profiler, Done);
    ReadSection := Res;
  end;


function SectionExists( const FileName: String; const Section: String): Boolean;
  var
    Profiler: pProfileScanner;
  begin
    Profiler := New( pProfileScanner, Create( FileName));
    SectionExists := Profiler^.Search( Section, '');
    Dispose( Profiler, Done);
  end;


end.