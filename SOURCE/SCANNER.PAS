{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       Scanner unit                                                    }
{                                              (c) Copyright 1997-1998  }
{                                   Iggor Khachko - hachko@icl.kazan.su }
{-----------------------------------------------------------------------}

{
  Дата создания: 20.09.97
}
unit Scanner;

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

interface

uses Dos, Objects, FileColl, Config, Errors, Symbols, Code, Tools;

const
  BufSize = 16384;

type

  pFileStack = ^tFileStack;
  tFileStack = record
    CurLine: LongInt;
    LastLineNumber: LongInt;
    PrevLine: LongInt;
    CurCol: Integer;
    PrevCol: Integer;
    FileName: String[80];
    Buffer: array [0..BufSize] of char;
    CurPos: Word;
    Next: pFileStack;
    CurFilePos: LongInt;
  end;

  tPreProcessToken = (
    cppIFDEF, cppIFNDEF, cppELSE
  );

  pPreProcessStack = ^tPreProcessStack;
  tPreProcessStack = object( tObject)
    PPTType: tPreProcessToken;
    Name: pString;
    Accept: Boolean;
    Next: pPreProcessStack;
    constructor Init( const aName: String; aType: tPreProcessToken; aAccept: Boolean;
      aNext: pPreProcessStack);
    destructor Done; virtual;
  end;

  pScanner = ^tScanner;
  tScanner = object(tObject)
    Status: Integer;
    Files: pFileStack;
    Switches: tSwitches;
    LastToken: tToken;
    LastLine: String;
    LastSymbol: pSymbol;
    LastSymbolName: tNameString;
    LastLevel: LongInt;
    CommentsLevel: Integer;
      wasPoint: Boolean;
    PreProcessStack: pPreProcessStack;

    { Глобальные символы }
    GlobalSymbols: pSymbolTable;
    { Стек функций (для реализации вложенных функций }
    CurrentFunction: pFunctionStack;
    {}
    MacrosTable: pSymbolTable;
    UnitName: tNameString;
    UnitSymbol: pUnitSymbol;
    { Название главного исходного файла }
    MainFileName: PathStr;

    { Основная функция между  последними begin ... end }
    MainFunc: pFunctionSymbol;
    { Текущий уровень вложенности подпрограмм }
    CurLevel: Byte;
    { уровень вложенности циклов }
    LoopLevel: LongInt;
    { уровень вложенности WITH и FOR }
    TempLevel: LongInt;
    { Стек таблиц символов }
    SymTableStack: pSymbolTableStack;
    { Опции для создаваемых символов public, prtoected и т.д. }
    SymbolsOptions: LongInt;
    { Текущий компилируемый объект(класс) }
    CurrentObject: pObjectDefinition;
    { Параметр метода SELF }
    SelfSymbol: pVariableSymbol;
    IsUnit: Boolean;
    LinkFiles: pFileCollection;

    constructor Init( const aFileName: String; const aUnitName: String);
    destructor Done; virtual;
    function GetLexeme: tToken;
    procedure Insert( const aFileName: String); virtual;
    procedure DeleteFile;
    procedure Reset;
    function CurChar: Char;
    function NextChar: Char;
    procedure SkipComments;
    procedure HandleSwitches;
    procedure Error(ErrorCode: Integer; Line, Col: LongInt; const Info: String); virtual;
    function Consume( aToken: tToken): Boolean; virtual;
    function NextToken: tToken;
    procedure PopPreProcess;
    procedure PushPreProcess( const aName: String; aType: tPreProcessToken;
      anAccept: Boolean);
    procedure SkipCode;

    { Ищет символ с заданным именем }
    function FindSymbol( const Name: String; var Level: LongInt): pSymbol;
    { Ищет символ с заданным алъясом }
    function FindWithAlias( const Name: String): pSymbol;
    { Ищет локальный символ }
    function FindLocalSymbol( const Name: String): pSymbol;
    { Ищет глобальный символ }
    function FindGlobalSymbol( const Name: String): pSymbol;

    { Виден или нет символ из данной области }
    function VisibleSymbol( Symbol: pSymbol): Boolean;

    { Создает основную подпрограмму }
    procedure CreateMainProcedure( const ProcName: tNameString);

    { Выдает имя для текущей таблицы символв }
    function GetSymbolTableName: String;

    {}
    procedure PushTable( Definition: pDefinition);
    {}
    procedure PopTable;

    { Возвращает тип заданного уровня WITH }
    function GetDefinition( Level: LongInt): pDefinition;

    { Загружает модули из списка USES }
    procedure LoadModules;
    { Загружает заданный модуль и все те модули, которые он использует }
    function LoadUnit( const aUnitName: String): Boolean;

    { Ищет функции с заданным именем и заданными параметрами }
    function FindFunction( const FuncName: tNameString; ParamColl: pDefCollection;
      ObjectCode: pCodeTree; var Level: LongInt; SymbolTable: pSymbolTable): pFunctionSymbol;

    { Оптимизирует выражение }
    procedure OptomizeExpression( var Code: pCodeTree);

    { Создает конечный ассемблерный файл }
    procedure WriteAsmFile;
    { Записывает в ассемблерный файл все функции }
    procedure WriteFunctions( SymbolTable: pSymbolTable; S: pStream);
  end;

implementation

uses StdLib, CodeOpt;

function IsKeyword( const Str: String; var Lex: tToken): Boolean;
  var
    First, Last, Cur: Integer;
  begin
    if Length(Str) <= 1 then
      begin
        IsKeyword := False;
        Exit;
      end;
    First := 0;
    Last := KeywordsCount - 1;
    while First <= Last do
      begin
        Cur := First + (Last - First) div 2;
        if Str = Keywords[Cur] then
          begin
            Lex := KeywordsToken[Cur];
            IsKeyWord := True;
            Exit;
          end
        else
          if Str > Keywords[Cur] then
            First := Cur + 1
          else
            Last := Cur - 1;
      end;
    IsKeyword := False;
  end;

constructor tPreProcessStack.Init( const aName: String; aType: tPreProcessToken; aAccept: Boolean;
      aNext: pPreProcessStack);
  begin
    inherited Init;
    Name := NewStr( aName);
    PPTType := aType;
    Accept := aAccept;
    Next := aNext;
  end;

destructor tPreProcessStack.Done;
  begin
    if Assigned( Name) then
      DisposeStr( Name);
    inherited Done;
  end;


constructor tScanner.Init( const aFileName: String; const aUnitName: String);

  procedure DoCopy( Item: pSymbol); {$IFDEF TP} far; {$ENDIF}
    begin
      MacrosTable^.Insert( New( pMacroSymbol, Init( Item^.SymbolName^)));
    end;

  begin
    inherited Init;
    LinkFiles := New( pFileCollection, Init( 0, 4));
    UnitName := UpStr( aUnitName);
    UnitSymbol:= New( pUnitSymbol, Init( UnitName, nil, LinkFiles));
    MacrosTable := New( pSymbolTable, Init( stMacrosTable, 8, 8));
    MainFileName := aFileName;
    Insert( aFileName);
    Switches := DefaultSwitches;
    {CurCol := 1;}
    wasPoint := False;

    MacrosTable^.Insert( New( pMacroSymbol, Init( 'PASCAL_PRO')));
    MacrosTable^.Insert( New( pMacroSymbol, Init( 'PASCALPRO')));
    MacrosTable^.Insert( New( pMacroSymbol, Init( 'PPRO')));
    MacrosTable^.Insert( New( pMacroSymbol, Init( TargetName)));
    {MacrosTable^.Insert( New( pMacroSymbol, Init( 'FLAT')));}
    {MacrosTable^.Insert( New( pMacroSymbol, Init( 'TASM')));}
    case Language of
      clRussian:
        MacrosTable^.Insert( New( pMacroSymbol, Init( '_RUSSIAN_')));
      clEnglish:
        MacrosTable^.Insert( New( pMacroSymbol, Init( '_ENGLISH_')));
    end;
    DefaultMacro^.ForEach( @DoCopy);

    LastToken := GetLexeme;
  end;

destructor tScanner.Done;
  var
    p: pFileStack;
  begin
    while Files <> nil do
      begin
        Inc( TotalLines, Files^.CurLine);
        StdLib.ClrLine;
        WriteLn( Files^.FileName, '(', Files^.CurLine, ')');
        p := Files;
        Files := Files^.Next;
        Dispose(p);
      end;
    {if OutFile <> nil then
      Dispose(OutFile, Done);}
    if Assigned( MacrosTable) then
      Dispose( MacrosTable, Done);
    inherited Done;
  end;

procedure tScanner.Insert( const aFileName: String);
  var
    p: pFileStack;
    fdi: pFileDateItem;
  begin
    if Assigned( UnitSymbol) and Assigned( UnitSymbol^.UsedFiles) then
      begin
        New( fdi);
        fdi^.FileName := NewStr( GetRelativePath( aFileName));
        fdi^.DateTime := GetFileTime( aFileName);
        UnitSymbol^.UsedFiles^.Insert( fdi);
      end;
    New(p);
    p^.FileName := GetRelativePath( aFileName);
    p^.Next := Files;
    p^.CurPos := 0;
    p^.Buffer[0] := #0;
    p^.CurLine := 1;
    p^.CurCol := 1;
    P^.LastLineNumber := 0;
    p^.CurFilePos := 0;
    Files := p;
    {Write( '                                                                   '#13);}
    ClrLine;
    {$IFDEF DEBUG}
    Write( Files^.FileName, '(', Files^.CurLine, ')');
    Write( MemAvail: 20, #13);
    {$ELSE}
    Write( Files^.FileName, '(', Files^.CurLine, ')'#13);
    {$ENDIF}
  end;

procedure tScanner.DeleteFile;
  var
    p: pFileStack;
  begin
    if Assigned( Files) then
      begin
        Inc( TotalLines, Files^.CurLine);
        ClrLine;
        Write( Files^.FileName, '(', Files^.CurLine, ')'#13#10);
        p := Files;
        Files := Files^.Next;
        Dispose(p);
      end;
  end;

procedure tScanner.Reset;
  begin
    while Assigned( Files) do
      DeleteFile;
    GlobalSymbols^.FreeAll;
    GlobalSymbols^.Root := nil;
    Insert( MainFileName);
    Switches := DefaultSwitches;
    wasPoint := False;
    LastToken := GetLexeme;
  end;

function tScanner.CurChar: Char;
  var
    S: Word;
    Stream: pStream;
  begin
    if (Files <> nil) then
      begin
        if Files^.Buffer[Files^.CurPos] = #0 then
          begin
            Stream := New( pDosStream, Init( Files^.FileName, stOpenRead));
            Stream^.Seek( Files^.CurFilePos);
            repeat
              if Stream^.GetSize{$IFDEF PPRO}(){$ENDIF} -
                Stream^.GetPos{$IFDEF PPRO}(){$ENDIF} > BufSize then
                S := BufSize
              else
                S := Stream^.GetSize{$IFDEF PPRO}(){$ENDIF} -
                  Stream^.GetPos{$IFDEF PPRO}(){$ENDIF};
              if S = 0 then
                begin
                  Files^.CurFilePos := Stream^.GetSize{$IFDEF PPRO}(){$ENDIF};
                  Dispose( Stream, Done{$IFDEF PPRO}(){$ENDIF});
                  if not Assigned( Files^.Next) then
                    begin
                      Files^.Buffer[0] := #26;
                      CurChar := #26;
                      Files^.Buffer[1] := #0;
                      Files^.CurPos := 0;
                      Exit;
                    end
                  else
                    begin
                      DeleteFile{$IFDEF PPRO}(){$ENDIF};
                      if Files^.Buffer[Files^.CurPos] = #0 then
                        S := 0
                      else
                        begin
                          CurChar := Files^.Buffer[ Files^.CurPos];
                          Exit;
                        end;
                      Stream := New( pDosStream, Init( Files^.FileName, stOpenRead));
                    end;
                end;
            until S > 0;
            Stream^.Read(Files^.Buffer, S);
            Files^.CurFilePos := Stream^.GetPos{$IFDEF PPRO}(){$ENDIF};
            Files^.CurPos := 0;
            Files^.Buffer[S] := #0;
            Dispose( Stream, Done{$IFDEF PPRO}(){$ENDIF});
          end;
        CurChar := Files^.Buffer[Files^.CurPos];
        Exit;
      end;
    CurChar := #26;
  end;

function tScanner.NextChar: Char;
  var
    c: char;
  begin
    if Files <> nil then {with Files^ do}
      begin
        if Files^.Buffer[Files^.CurPos] <> #0 then
          Inc( Files^.CurPos);
        NextChar := CurChar;
        Inc( Files^.CurCol);
        if Files^.Buffer[ Files^.CurPos] = #10 then
          begin
            Inc( Files^.CurLine);
            Files^.CurCol := 0;
            if Files^.CurLine - Files^.LastLineNumber >= 128 then
              begin
                Files^.LastLineNumber := Files^.CurLine;
                Write( Files^.FileName, '(', Files^.CurLine, ')'#13);
              end;
          end;
      end;
  end;

procedure tScanner.HandleSwitches;

  function ReadSwitchName: String;
    var
      Str: String;
      C: Char;
    begin
      Str := '';
      C := UpCase(NextChar);
      while ((C >= 'A') and (C <= 'Z')) or (C = '_') do
        begin
          Str := Str + C;
          C := NextChar{$IFDEF PPRO}(){$ENDIF};
        end;
      while CurChar{$IFDEF PPRO}(){$ENDIF} in [' ', #10, #13, #9] do
        NextChar{$IFDEF PPRO}(){$ENDIF};
      ReadSwitchName := Str;
    end;

  function ReadName: String;
    var
      Str: String;
      C: Char;
    begin
      Str := '';
      C := UpCase( CurChar);
      while C = ' ' do C := NextChar;
      while C in ['A'..'Z', '0'..'9', '_'] do
        begin
          Str := Str + C;
          C := NextChar;
        end;
      while CurChar in [' ', #10, #13, #9] do
        NextChar;
      ReadName := Str;
    end;

  function ReadFileName: String;
    var
      C: Char;
      Str: String;
    begin
      while CurChar in [' ', #10, #13, #9] do
        NextChar;
      C := UpCase( CurChar);
      Str := '';
      while not ( C in [' ', '}', '{', #13, #10, #9]) do
        begin
          Str := Str + C;
          C := UpCase( NextChar);
        end;
      while CurChar in [' ', #10, #13, #9] do
        NextChar;
      ReadFileName := Str;
    end;

  var
    sStr: String;
    DefName: String;
    Symbol: pSymbol;
    B: Boolean;

  begin
    sStr := ReadSwitchName;

    if (sStr = 'IFDEF') then
      begin
        DefName := ReadName;
        if DefName = '' then
          Error( erIdentifierExpected, Files^.CurLine, Files^.CurCol, '');
        Symbol := MacrosTable^.FindSymbol( DefName);
        PushPreProcess( DefName, cppIFDEF, Assigned( Symbol) );
      end
    else if (sStr = 'ELSE') then
      begin
        if not Assigned( PreProcessStack) then
          Error( erMisplacedConditionalDirective, Files^.PrevLine, Files^.PrevCol, sStr);
        B := not PreProcessStack^.Accept;
        DefName := PreProcessStack^.Name^;
        PopPreProcess;
        PushPreProcess( DefName, cppELSE, B);
      end
    else if (sStr = 'IFNDEF') then
      begin
        DefName := ReadName;
        if DefName = '' then
          Error( erIdentifierExpected, Files^.CurLine, Files^.CurCol, '');
        Symbol := MacrosTable^.FindSymbol( DefName);
        PushPreProcess( DefName, cppIFDEF, not Assigned( Symbol) );
      end
    else if (sStr = 'ENDIF') then
      begin
        if not Assigned( PreProcessStack) then
          Error( erMisplacedConditionalDirective, Files^.PrevLine, Files^.PrevCol, sStr);
        PopPreProcess;
      end
    else
    if Assigned( PreProcessStack) and not PreProcessStack^.Accept then
      Exit
    else
    if sStr = 'DEFINE' then
      begin
        DefName := ReadName;
        if DefName = '' then
          Error( erIdentifierExpected, Files^.CurLine, Files^.CurCol, '');
        MacrosTable^.Insert( New( pMacroSymbol, Init( DefName)));
      end
    else if sStr = 'UNDEF' then
      begin
        DefName := ReadName;
        if DefName = '' then
          Error( erIdentifierExpected, Files^.CurLine, Files^.CurCol, '');
        Symbol := MacrosTable^.FindSymbol( DefName);
        if Assigned( Symbol) then
          MacrosTable^.Free( Symbol);
      end
    else if sStr = 'WARNING' then
      begin
      end
    else if sStr = 'ERROR' then
      begin
        sStr := '';
        repeat
          sStr := sStr + CurChar;
        until NextChar in [ #0..#26, '}'];
        Error( erErrorDirective, Files^.CurLine, Files^.CurCol, sStr);
      end
    else if sStr = 'I' then
      begin
        sStr := ReadFileName;
        if not FindFile( sStr, sStr, IncludeSearchPath) then
          Error( erFileNotFound, Files^.PrevLine, Files^.PrevCol, sStr);
        Dec( CommentsLevel);
        while not (CurChar in ['}', #26]) do
          NextChar;
        NextChar;
        Insert( sStr);
      end
    else if sStr = 'L' then
      begin
        sStr := ReadFileName;
        if not FindFile( sStr, sStr, ObjSearchPath) then
          Error( erFileNotFound, Files^.PrevLine, Files^.PrevCol, sStr);
        LinkFiles^.Insert( NewStr( sStr));
        while not (CurChar in ['}', #26]) do NextChar;
      end
    {else if sStr = 'F' then
      begin
      end
    else if sStr = 'R' then
      begin
      end
    else if sStr = 'V' then
      begin
      end}
    else
      Error( erInvalidCompilerDirective, Files^.CurLine, Files^.CurCol, sStr);
  end;

procedure tScanner.SkipComments;
  begin
    Inc(CommentsLevel);

    while True do
      begin
        if (NextChar = '$') and (CommentsLevel = 1) then
          begin
            HandleSwitches;
            if CommentsLevel <= 0 then
              Exit;
          end;
        while CurChar <> '}' do
          begin
            case CurChar of
              '{':
                SkipComments{$IFDEF PPRO}(){$ENDIF};
              {#10:
                Inc(CurLine);}
              #26:
                Error( erUnexpectedEndOfFile, Files^.PrevLine, Files^.PrevCol, '');
            end;
            NextChar;
          end;
        if CurChar{$IFDEF PPRO}(){$ENDIF} = '}' then
          begin
            Dec( CommentsLevel);
            if NextChar{$IFDEF PPRO}(){$ENDIF} <> '{' then break;
            Inc( CommentsLevel);
          end;
      end;
  end;

function tScanner.GetLexeme: tToken;
  var
    S: String;
    L: LongInt;
    I: Integer;
  begin
    LastSymbol := nil;
    LastLevel := 0;
    LastSymbolName[ 0] := #0;
    Files^.PrevCol := Files^.CurCol;
    Files^.PrevLine := Files^.CurLine;
    if wasPoint then
    begin
      if CurChar = '.' then
        begin
          Files^.PrevCol := Files^.CurCol - 1;
          NextChar;
          LastLine := '..';
          LastToken := ctPointPoint;
        end
      else
        begin
          LastLine := '.';
          LastToken := ctPoint;
        end;
      wasPoint := False;
      GetLexeme := LastToken;
      Exit;
    end;
    if CurChar = '{' then
      SkipComments;
    while CurChar in [' ', #9, #10, #13] do
      begin
        if NextChar = '{' then
          SkipComments;
      end;
    Files^.PrevCol :=  Files^.CurCol;
    Files^.PrevLine := Files^.CurLine;
    case CurChar of
      'a'..'z', 'A'..'Z', '_':
        begin
          LastLine := UpCase(CurChar);
          while NextChar in ['A'..'Z', 'a'..'z', '0'..'9', '_'] do
            begin
              LastLine := LastLine + UpCase(CurChar);
            end;
          if IsKeyWord(LastLine, LastToken) then
            begin
              if CurChar = '=' then
                if LastToken = ctAnd then
                  begin
                    NextChar;
                    LastToken := ctAndAsn;
                    LastLine := LastLine + '=';
                  end
                else if LastToken = ctOr then
                  begin
                    NextChar;
                    LastToken := ctOrAsn;
                    LastLine := LastLine + '=';
                  end
                else if LastToken = ctXor then
                  begin
                    NextChar;
                    LastToken := ctXorAsn;
                    LastLine := LastLine + '=';
                  end
                else if LastToken = ctShl then
                  begin
                    NextChar;
                    LastToken := ctShlAsn;
                    LastLine := LastLine + '=';
                  end
                else if LastToken = ctShr then
                  begin
                    NextChar;
                    LastToken := ctShrAsn;
                    LastLine := LastLine + '=';
                  end
                else if LastToken = ctMod then
                  begin
                    NextChar;
                    LastToken := ctModAsn;
                    LastLine := LastLine + '=';
                  end
                else if LastToken = ctDiv then
                  begin
                    NextChar;
                    LastToken := ctDivAsn;
                    LastLine := LastLine + '=';
                  end;
              GetLexeme := LastToken
            end
          else
            GetLexeme := ctIdentifier;
          Exit;
        end;
      ';':
        begin
          LastLine := ';';
          NextChar;
          LastToken := ctSemiColon;
          GetLexeme := ctSemiColon;
          Exit;
        end;
      ':':
        begin
          LastLine := ':';
          LastToken := ctColon;
          if NextChar = '=' then
            begin
              LastLine := ':=';
              LastToken := ctAssignment;
              NextChar;
            end;
          GetLexeme := LastToken;
          Exit;
        end;
      '.':
        begin
          if NextChar = '.' then
            begin
              LastToken := ctPointPoint;
              NextChar;
              LastLine := '..';
            end
          else
            begin
              LastToken := ctPoint;
              LastLine := '.';
            end;
          GetLexeme := LastToken;
          Exit;
        end;
      ',':
        begin
          NextChar;
          LastLine := ',';
          LastToken := ctComma;
          GetLexeme := LastToken;
        end;
      '*':
        begin
          if NextChar = '=' then
            begin
              LastLine := '*=';
              LastToken := ctStarAsn;
              NextChar;
            end
          else
            begin
              LastLine := '*';
              LastToken := ctStar;
            end;
          GetLexeme := LastToken;
          Exit;
        end;
      '/':
        begin
          if NextChar = '=' then
            begin
              LastLine := '/=';
              LastToken := ctSlashAsn;
              NextChar;
            end
          else
            begin
              LastLine := '/';
              LastToken := ctSlash;
            end;
          GetLexeme := LastToken;
          Exit;
        end;
      '+':
        begin
          if NextChar = '=' then
            begin
              LastLine := '+=';
              LastToken := ctPlusAsn;
              NextChar;
            end
          else
            begin
              LastLine := '+';
              LastToken := ctPlus;
            end;
          GetLexeme := LastToken;
          Exit;
        end;
      '-':
        begin
          if NextChar = '=' then
            begin
              LastLine := '-=';
              LastToken := ctMinusAsn;
              NextChar;
            end
          else
            begin
              LastLine := '-';
              LastToken := ctMinus;
            end;
          GetLexeme := LastToken;
          Exit;
        end;
      '0'..'9':
        begin
          LastLine := CurChar{$IFDEF PPRO}(){$ENDIF};
          LastToken := ctIntConst;
          while NextChar{$IFDEF PPRO}(){$ENDIF} in ['0'..'9'] do
            LastLine := LastLine + CurChar{$IFDEF PPRO}(){$ENDIF};
          if (CurChar{$IFDEF PPRO}(){$ENDIF} = '.') or
            (UpCase( CurChar{$IFDEF PPRO}(){$ENDIF}) = 'E') then
            begin
              if CurChar = '.' then
                if NextChar = '.' then
                  wasPoint := True
                else
                  begin
                    LastLine := LastLine + '.';
                    LastToken := ctRealConst;
                  end;
              while CurChar{$IFDEF PPRO}(){$ENDIF} in ['0'..'9'] do
                begin
                  LastLine := LastLine + CurChar{$IFDEF PPRO}(){$ENDIF};
                  NextChar{$IFDEF PPRO}(){$ENDIF};
                end;
              if (UpCase(CurChar{$IFDEF PPRO}(){$ENDIF}) = 'E') then
                begin
                  LastLine := LastLine + 'E';
                  NextChar{$IFDEF PPRO}(){$ENDIF};
                  if (CurChar{$IFDEF PPRO}(){$ENDIF} = '+') or
                    (CurChar{$IFDEF PPRO}(){$ENDIF} = '-') then
                    begin
                      LastLine := LastLine + CurChar{$IFDEF PPRO}(){$ENDIF};
                      NextChar{$IFDEF PPRO}(){$ENDIF};
                    end;
                  while CurChar{$IFDEF PPRO}(){$ENDIF} in ['0'..'9'] do
                    begin
                      LastLine := LastLine + CurChar{$IFDEF PPRO}(){$ENDIF};
                      NextChar{$IFDEF PPRO}(){$ENDIF};
                    end;
                  LastToken := ctRealConst;
                end
            end;
          GetLexeme := LastToken;
          Exit;
        end;
      '=':
        begin
          LastLine := '=';
          NextChar;
          LastToken := ctEqual;
          GetLexeme := LastToken;
        end;
      '(':
        begin
          NextChar{$IFDEF PPRO}(){$ENDIF};
          LastLine := '(';
          LastToken := ctLParen;
          GetLexeme := LastToken;
        end;
      ')':
        begin
          NextChar{$IFDEF PPRO}(){$ENDIF};
          LastLine := ')';
          LastToken := ctRParen;
          GetLexeme := LastToken;
        end;
      '$':
        begin
          LastLine := '$';
          while UpCase( NextChar) in ['0'..'9', 'A'..'F'] do
            LastLine := LastLine + CurChar;
          LastToken := ctIntConst;
          GetLexeme := LastToken;
        end;
      '#', '''':
        begin
          LastLine := '''';
{writeln( ' lex - string const');}
          while CurChar in [ '#', ''''] do
            begin
              case CurChar of
                '#':
                  begin
                    S := '';
                    if NextChar = '$' then
                      begin
                        S := '$';
                        while UpCase( NextChar{$IFDEF PPRO}(){$ENDIF}) in ['0'..'9', 'A'..'F'] do
                          S := S + CurChar{$IFDEF PPRO}(){$ENDIF};
                      end
                    else
                      begin
                        while CurChar{$IFDEF PPRO}(){$ENDIF} in ['0'..'9'] do
                          begin
                            S := S + CurChar{$IFDEF PPRO}(){$ENDIF};
                            NextChar{$IFDEF PPRO}(){$ENDIF};
                          end;
                      end;
                    Val( S, L, I);
                    LastLine := LastLine + Char( L);
                  end;
                '''':
                  begin
                    S := '';
{writeln( ' reading string ');}
                    while True do
                      begin
                        if NextChar in [#10, #13] then
                          Error( erStringConstantExceedsLine, Files^.CurLine, Files^.CurCol, '');
{writeln( 'curchar = "', curchar, '"');}
                        if (CurChar = '''') then
                          if NextChar <> '''' then break;
                        S := S + CurChar;
{writeln( '"', s, '"');}
                      end;
                    LastLine := LastLine + S;
{writeln( ' string was read ');}
                  end;
              end;
            end;
          LastLine := LastLine + '''';
          if Length(LastLine) = 3 then
            LastToken := ctCharConst
          else
            LastToken := ctStringConst;
          GetLexeme := LastToken;
{writeln( ' ok ');}
        end;

      '>':
        begin
          LastLine := '>';
          LastToken := ctGreater;
          if NextChar{$IFDEF PPRO}(){$ENDIF} = '=' then
            begin
              LastLine := '>=';
              LastToken := ctGreaterEq;
              NextChar{$IFDEF PPRO}(){$ENDIF};
            end;
          GetLexeme := LastToken;
        end;
      '<':
        begin
          LastLine := '<';
          LastToken := ctLess;
          if NextChar{$IFDEF PPRO}(){$ENDIF} = '=' then
            begin
              LastLine := '<=';
              LastToken := ctLessEq;
              NextChar{$IFDEF PPRO}(){$ENDIF};
            end
          else if CurChar{$IFDEF PPRO}(){$ENDIF} = '>' then
            begin
              LastLine := '<>';
              LastToken := ctUnequal;
              NextChar{$IFDEF PPRO}(){$ENDIF};
            end;
          GetLexeme := LastToken;
        end;
      '[':
        begin
          LastLine := '[';
          LastToken := ctLBracket;
          NextChar{$IFDEF PPRO}(){$ENDIF};
          GetLexeme := LastToken;
        end;
      ']':
        begin
          LastLine := ']';
          LastToken := ctRBracket;
          NextChar{$IFDEF PPRO}(){$ENDIF};
          GetLexeme := LastToken;
        end;
      '^':
        begin
          LastLine := '^';
          LastToken := ctCarret;
          NextChar{$IFDEF PPRO}(){$ENDIF};
          GetLexeme := LastToken;
        end;
      '@':
        begin
          LastLine := '@';
          LastToken := ctAt;
          NextChar{$IFDEF PPRO}(){$ENDIF};
          GetLexeme := LastToken;
        end;
      else
        begin
          Error( erSyntaxError, Files^.CurLine, Files^.CurCol, '');
        end;
    end;
  end;

procedure tScanner.Error(ErrorCode: Integer; Line, Col: LongInt; const Info: String);
  begin
    Status := ErrorCode;
    if ErrorCode <> 0 then
      begin
        WriteLn;
        case Language of
          clRussian:
            begin
              Write('Ошибка: ''', GetErrorMessage( ErrorCode) );
              if Info <> '' then
                Write( ': "' + Info + '"');
              WriteLn('''.'#13#10' Файл ''',
                Files^.FileName, ''' Строка ', Line, ' , столбец ',
                  Col);
            end;
          clEnglish:
            begin
              Write('Error: ''',  GetErrorMessage( ErrorCode) );
              if Info <> '' then
                Write( ': "', Info, '"');
              WriteLn('''.'#13#10' File ''',
                Files^.FileName, ''' Line ', Line, ' , Column ',
                  Col);
            end;
        end;
        WriteLn;
        {Dispose( ListFile, Done);}
        Dispose( BatchFile, Done);
        Halt( ErrorCode);
      end;
  end;

function tScanner.Consume( aToken: tToken): Boolean;
  var
    ErrorCode: Integer;
  begin
{writeln( 'scanner.tscanner.consume');}
    if LastToken <> aToken then
      begin
{writeln( 'something wrong');}
        Consume := False;
        case aToken of
          ctIdentifier: ErrorCode := erIdentifierExpected;
          ctIntConst: ErrorCode := erIntegerConstantExpected;
          ctRealConst: ErrorCode := erIntegerOrRealConstantExpected;
          ctBEGIN: ErrorCode := erBEGINExpected;
          ctEND: ErrorCode := erENDExpected;
          ctDO: ErrorCode := erDOExpected;
          ctOF: ErrorCode := erOFExpected;
          ctINTERFACE: ErrorCode := erINTERFACEExpected;
          ctTHEN: ErrorCode := erTHENExpected;
          ctIMPLEMENTATION: ErrorCode := erIMPLEMENTATIONExpected;
          ctUNIT: ErrorCode := erUNITExpected;
          ctSemicolon: ErrorCode := erSemicolonExpected;
          ctColon: ErrorCode := erColonExpected;
          ctComma: ErrorCode := erCommaExpected;
          ctLParen: ErrorCode := erLeftParenExpected;
          ctRParen: ErrorCode := erRightParenExpected;
          ctEqual: ErrorCode := erEqualExpected;
          ctAssignment: ErrorCode := erAssignmentExpected;
          ctLBracket: ErrorCode := erLeftBracketExpected;
          ctRBracket: ErrorCode := erRightBracketExpected;
          ctPoint: ErrorCode := erPointExpected;
          ctPointPoint: ErrorCode := erPointPointExpected;
          ctStringConst: Errorcode := erStringConstantExpected;
          ctVIRTUAL: ErrorCode := erVIRTUALExpected;
          ctASM: ErrorCode := erASMExpected;
        else
          ErrorCode := erInternalError;
        end;
        Error( ErrorCode, Files^.PrevLine, Files^.PrevCol, '');
        Exit;
      end;
{writeln( 'get lexeme');}
    LastToken := GetLexeme;
{writeln( 'lexeme was got');}
    Consume := True;
  end;

function tScanner.NextToken: tToken;
  begin
    LastToken := GetLexeme{$IFDEF PPRO}(){$ENDIF};
    NextToken := LastToken;
  end;

procedure tScanner.PushPreProcess( const aName: String; aType: tPreProcessToken;
    anAccept: Boolean);
  begin
    if Assigned( PreProcessStack) and not PreProcessStack^.Accept then
      anAccept := False;
    PreProcessStack := New( pPreProcessStack, Init(
      aName, aType, anAccept, PreProcessStack));
    if not anAccept then
      SkipCode{$IFDEF PPRO}(){$ENDIF};
  end;

procedure tScanner.PopPreProcess;
  var
    P: pPreProcessStack;
  begin
    P := PreProcessStack;
    if Assigned( P) then
      begin
        PreProcessStack := P^.Next;
        Dispose( P, Done{$IFDEF PPRO}(){$ENDIF});
      end;
  end;

procedure tScanner.SkipCode;
  begin
    if CurChar{$IFDEF PPRO}(){$ENDIF} <> '}' then
      SkipComments{$IFDEF PPRO}(){$ENDIF}
    else
      NextChar{$IFDEF PPRO}(){$ENDIF};
    Dec( CommentsLevel);
    repeat
      while CurChar{$IFDEF PPRO}(){$ENDIF} in [#10, #13, ' ', #9] do
        NextChar{$IFDEF PPRO}(){$ENDIF};
      case CurChar{$IFDEF PPRO}(){$ENDIF} of
        #26:
          Error( erUnexpectedEndOfFile, Files^.PrevLine, Files^.PrevCol, '');
        '{':
          SkipComments{$IFDEF PPRO}(){$ENDIF};
        else
          NextToken{$IFDEF PPRO}(){$ENDIF};
      end;
    until not Assigned( PreProcessStack) or PreProcessStack^.Accept;
  end;


function tScanner.FindSymbol( const Name: String; var Level: LongInt): pSymbol;
  var
    L, I: tIndex;
    FStack: pFunctionStack;
    Sym: pSymbol;
    P: pSymbolTableStack;
    Def: pDefinition;
  begin
    P := SymTableStack;
    if LastSymbolName = Name then
      begin
        FindSymbol := LastSymbol;
        Level := LastLevel;
        Exit;
      end;
    while Assigned( P) do
      begin
        case P^.Definition^.DefType of
          cRecordDefinition:
            begin
              Sym := pRecordDefinition( P^.Definition)^.Fields^.Search( Name);
              if Assigned( Sym) then
                begin
                  FindSymbol := Sym;
                  Level := P^.Level;
                  LastSymbolName := Name;
                  LastSymbol := Sym;
                  LastLevel := P^.Level;
                  Exit;
                end;
            end;
          cObjectDefinition:
            begin
              Def := P^.Definition;
              while Assigned( Def) do
                begin
                  Sym := pObjectDefinition( Def)^.PublicSymbols^.Search( Name);
                  if Assigned( Sym) then
                    begin
                      if VisibleSymbol( Sym) then
                        begin
                          FindSymbol := Sym;
                          Level := P^.Level;
                          LastSymbolName := Name;
                          LastSymbol := Sym;
                          LastLevel := P^.Level;
                          Exit;
                        end;
                    end;
                  Def := pObjectDefinition( Def)^.Ancestor;
                end;
            end;
          cFunctionDefinition:
            begin
              if Assigned( pFunctionDefinition( P^.Definition)^.LocalSymbols) then
                begin
                  Sym := pFunctionDefinition( P^.Definition)^.LocalSymbols^.Search( Name);
                  if Assigned( Sym) then
                  begin
                    FindSymbol := Sym;
                    Level := P^.Level;
                    LastSymbolName := Name;
                    LastSymbol := Sym;
                    LastLevel := P^.Level;
                    Exit;
                  end;
                end;
            end;
        end;
        P := P^.Next;
      end;
    if Assigned( CurrentObject) then
      begin
        Def := CurrentObject;
        while Assigned( Def) do
          begin
            Sym := pObjectDefinition( Def)^.PublicSymbols^.Search( Name);
            if Assigned( Sym) then
              begin
                if VisibleSymbol( Sym) then
                  begin
                    FindSymbol := Sym;
                    Level := -1;
                    LastSymbolName := Name;
                    LastSymbol := Sym;
                    LastLevel := -1;
                    Exit;
                  end;
              end;
            Def := pObjectDefinition( Def)^.Ancestor;
          end;
      end;
    FindSymbol := nil;
    {FStack := CurrentFunction;
    while Assigned( FStack) do
      begin
        if Assigned( FStack^.Func) and
          Assigned( FStack^.Func^.Definition) then
          begin
            if Assigned( pFunctionDefinition( FStack^.Func^.Definition)^.LocalSymbols) then
              begin
                Sym := pFunctionDefinition( FStack^.Func^.Definition)^.LocalSymbols^.Search( Name);
                if Assigned( Sym) then
                  begin
                    FindSymbol := Sym;
                    Exit;
                  end;
              end;
          end;
        FStack := FStack^.Next;
      end;}
    if Assigned( GlobalSymbols) then
      begin
        Sym := GlobalSymbols^.Search( Name);
        if Assigned( Sym) then
          begin
            FindSymbol := Sym;
            Level := 0;
            LastSymbolName := Name;
            LastSymbol := Sym;
            LastLevel := 0;
            Exit;
          end;
        for L := GlobalSymbols^.Count - 1 downto 0 do
          begin
            Sym := pSymbol( GlobalSymbols^.At(L));
            if Sym^._Type = cUnitSymbol then
              begin
                Sym := pUnitSymbol( Sym)^.UnitSymbols^.Search( Name);
                if Assigned( Sym) then
                  begin
                    if VisibleSymbol( Sym) then
                      begin
                        FindSymbol := Sym;
                        Level := 0;
                        LastSymbolName := Name;
                        LastSymbol := Sym;
                        LastLevel := 0;
                      end;
                    Exit;
                  end;
              end;
          end;
      end;
  end;

function tScanner.FindWithAlias( const Name: String): pSymbol;
  var
    L, I: Integer;
    FStack: pFunctionStack;
    Sym: pSymbol;
  begin
    FindWithAlias := nil;
    if LastSymbolName = Name then
      begin
        FindWithAlias := LastSymbol;
        Exit;
      end;
    FStack := CurrentFunction;
    while Assigned( FStack) do
      begin
        if Assigned( FStack^.Func) and
          Assigned( FStack^.Func^.Definition) then
          begin
            if Assigned( pFunctionDefinition( FStack^.Func^.Definition)^.LocalSymbols) then
              begin
                Sym := pFunctionDefinition( FStack^.Func^.Definition)^.LocalSymbols^.FindWithAlias( Name);
                if Assigned( Sym) then
                  begin
                    FindWithAlias := Sym;
                    LastSymbolName := Name;
                    LastSymbol := Sym;
                    LastLevel := 0;
                    Exit;
                  end;
              end;
          end;
        FStack := FStack^.Next;
      end;
    if Assigned( GlobalSymbols) then
      begin
        Sym := GlobalSymbols^.FindWithAlias( Name);
        if Assigned( Sym) then
          begin
            FindWithAlias := Sym;
            LastSymbolName := Name;
            LastSymbol := Sym;
            LastLevel := 0;
            Exit;
          end;
        for L := 0 to GlobalSymbols^.Count - 1 do
          begin
            Sym := pSymbol( GlobalSymbols^.At(L));
            if Sym^._Type = cUnitSymbol then
              begin
                Sym := pUnitSymbol( Sym)^.UnitSymbols^.FindWithAlias( Name);
                if Assigned( Sym) then
                  begin
                    FindWithAlias := Sym;
                    LastSymbolName := Name;
                    LastSymbol := Sym;
                    LastLevel := 0;
                    Exit;
                  end;
              end;
          end;
      end;
  end;

function tScanner.FindLocalSymbol( const Name: String): pSymbol;
  var
    L: tIndex;
    Sym: pSymbol;
  begin
    FindLocalSymbol := nil;
    if LastSymbolName = Name then
      begin
        FindLocalSymbol := LastSymbol;
        Exit;
      end;
    if Assigned( CurrentFunction) then
      begin
        if Assigned( CurrentFunction^.Func) and
          Assigned( CurrentFunction^.Func^.Definition) then
          begin
            if CurrentFunction^.Func^.Name{$IFDEF PPRO}(){$ENDIF} = Name then
              begin
                FindLocalSymbol := CurrentFunction^.Func;
                LastSymbolName := Name;
                LastSymbol := Sym;
                LastLevel := 0;
                Exit;
              end;
            if Assigned( CurrentFunction^.Func^.Definition^.LocalSymbols) then
              begin
                Sym := pFunctionDefinition( CurrentFunction^.Func^.Definition)^.LocalSymbols^.Search( Name);
                if Assigned( Sym) then
                  begin
                    FindLocalSymbol := Sym;
                    LastSymbolName := Name;
                    LastSymbol := Sym;
                    LastLevel := 0;
                    Exit;
                  end;
              end;
          end;
        Exit;
      end;
    if Assigned( GlobalSymbols) then
      begin
        Sym := GlobalSymbols^.Search( Name);
        if Assigned( Sym) then
          begin
            FindLocalSymbol := Sym;
            LastSymbolName := Name;
            LastSymbol := Sym;
            LastLevel := 0;
            Exit;
          end;
      end;
  end;

function tScanner.FindGlobalSymbol( const Name: String): pSymbol;
  var
    L: tIndex;
  begin
    FindGlobalSymbol := nil;
    if Assigned( GlobalSymbols) then
      {if GlobalSymbols^.Search( @Name, L) then}
        begin
          FindGlobalSymbol := GlobalSymbols^.Search( Name);
        end;
  end;


function tScanner.VisibleSymbol( Symbol: pSymbol): Boolean;
  begin
    VisibleSymbol := False;
    if Assigned( Symbol) then
      case Symbol^.Options of
        csoPublicSymbol:
          VisibleSymbol := True;
        csoPrivateSymbol:
          VisibleSymbol := GetUnitTable( Symbol) = GlobalSymbols;
        csoProtectedSymbol:
          VisibleSymbol := (GetUnitTable( Symbol) = GlobalSymbols) or
            (Assigned( CurrentObject) and Assigned( Symbol^.Owner) and
            (Symbol^.Owner^.SymbolTableType = stObjectTable) and
            Assigned( Symbol^.Owner^.Owner) and
            (pDefinition( Symbol^.Owner^.Owner)^.DefType = cObjectDefinition) and
            IsAncestor( pObjectDefinition( Symbol^.Owner^.Owner), CurrentObject) );
      end;
  end;


procedure tScanner.CreateMainProcedure( const ProcName: tNameString);
  begin
{    if CurrentFunction <> nil then
      begin}
        New(CurrentFunction);
        CurrentFunction^.Func := New(pFunctionSymbol, Init(ProcName, True, csoPublicSymbol));
        CurrentFunction^.Next := nil;
        MainFunc := CurrentFunction^.Func;
        MainFunc^.Definition := New( pMainFunctionDefinition,
          Init);
        GlobalSymbols := MainFunc^.Definition^.LocalSymbols;
{      end;}
  end;

function tScanner.GetSymbolTableName: String;
  var
    FuncStack: pFunctionStack;
    Str: String;
  begin
    FuncStack := CurrentFunction;
    Str := '_';
    if Assigned( FUncStack) then
      while Assigned( FuncStack^.Next) do
        begin
          Str := '_' + FuncStack^.Func^.Name + Str;
          FuncStack := FuncStack^.Next;
        end;
    GetSymbolTableName := Str;
  end;


procedure tScanner.PushTable( Definition: pDefinition);
  var
    P: pSymbolTableStack;
  begin
    {Inc( TempLevel);}
    New( P);
    P^.Next := SymTableStack;
    P^.Level := TempLevel;
    P^.Definition := Definition;
    SymTableStack := P;
  end;

procedure tScanner.PopTable;
  var
    P: pSymbolTableStack;
  begin
    if Assigned( SymTableStack) then
      begin
        P := SymTableStack;
        SymTableStack := P^.Next;
        Dispose( P);
        {Dec( TempLevel);}
      end;
  end;


function tScanner.GetDefinition( Level: LongInt): pDefinition;
  var
    STstack: pSymbolTableStack;
  begin
    STstack := SymTableStack;
    while Assigned( STstack) do
      begin
        if STstack^.Level = Level then
          begin
            GetDefinition := STstack^.Definition;
            Exit;
          end;
        STstack := STstack^.Next;
      end;
    GetDefinition := nil;
  end;

procedure tScanner.LoadModules;
  var
    UName: tNameString;
  begin
    Consume( ctUses);
    repeat
      if LastToken <> ctIdentifier then
        Error( erIdentifierExpected, Files^.PrevLine, Files^.PrevCol, '');
      UName := LastLine;
      LoadUnit( UName);
      if not Assigned( Files) then
        Exit;
      Consume( ctIdentifier);
      if LastToken <> ctSemicolon then
        Consume( ctComma)
      else break;
    until False;
    Consume( ctSemicolon);
  end;

function tScanner.LoadUnit( const aUnitName: String): Boolean;
  var
    USymbol: pUnitSymbol;
    FileName: PathStr;
    I: tIndex;
    L: LongInt;
    {S: pBufStream;
    Header: String;
    UsedFiles: pFileDateCollection;
    fdi: pFileDateItem;}
    UI: pUnitItem;
  begin
    if Assigned( UnitSymbol) and Assigned( UnitSymbol^.UsedUnits) then
      {if UnitSymbol^.UsedUnits^.Search( @aUnitName, I) then}
      if FindSymbol( aUnitName, L) <> nil then
        Error( erDuplicateIdentifier, Files^.PrevLine, Files^.PrevCol, aUnitName)
      else
        UnitSymbol^.UsedUnits^.Insert( NewStr( aUnitName));


    LoadUnitFile( aUnitName, aUnitName);
    if not Assigned( Files) then
      begin
        LoadUnit := True;
        Exit;
      end;
    if Assigned( UnitCollection) and
      UnitCollection^.Search( @aUnitName, I) then
      begin
        LoadUnit := True;
        UI := pUnitItem( UnitCollection^.At( I));
        if IsUnit and GlobalSymbols^.IsCompileInterface and
          UI^.IsUnitCompiled and
          not UI^.IsInterfaceReady and
          Assigned( UI^.UsedUnits) and
          (UI^.UsedUnits^.IndexOf( @UnitName) >= 0) then
            Error( erCircularUnitReference, Files^.PrevLine, Files^.PrevCol, aUnitName);
        USymbol := New( pUnitSymbol, Init(
          aUnitName, UI^.SymbolTable, nil) );
        {USymbol := pUnitSymbol( GlobalSymbols^.FindSymbol( aUnitName));
        Dispose( USymbol^.UnitSymbols, Done);
        USymbol^.UnitSymbols := UI^.SymbolTable;}
        if not Assigned( USymbol^.UnitSymbols^.Owner) then
          USymbol^.UnitSymbols^.Owner := USymbol;
        USymbol^.Owner := GlobalSymbols;
        GlobalSymbols^.Insert( USymbol);
        Exit;
      end;
    USymbol := New( pUnitSymbol, LoadUnit( aUnitName, aUnitName ));
    USymbol^.Owner := GlobalSymbols;
    GlobalSymbols^.Insert( USymbol);
    LoadUnit := True;
  end;


function tScanner.FindFunction( const FuncName: tNameString; ParamColl: pDefCollection;
    ObjectCode: pCodeTree; var Level: LongInt; SymbolTable: pSymbolTable): pFunctionSymbol;
  var
    FuncSym: pFunctionSymbol;
    Sym: pUnitSymbol;
    Pos: tIndex;
    FuncStack: pFunctionStack;
    CurTable: pSymbolTable;
    FuncColl, Coll: pFunctionStack;
    pColl: ^pFunctionStack;
    I: tIndex;
    STStack: pSymbolTableStack;
    {ObjDef: pObjectDefinition;}

  procedure ScanObjectMethods( ObjDef: pObjectDefinition; aLevel: LongInt);
    var
      I: tIndex;
    begin
      while Assigned( ObjDef) do
        begin
          FuncSym := ObjDef^.PublicSymbols^.Search( FuncName);
          while Assigned( FuncSym) do
            begin
              if VisibleSymbol( FuncSym) and
                IsCompatible( FuncSym^.Definition^.ParamColl, ParamColl) then
                begin
                  New( pColl^);
                  pColl^^.Func := FuncSym;
                  pColl^^.Next := nil;
                  pColl^^.Level := aLevel;
                  pColl := @pColl^^.Next;
                end;
              FuncSym := FuncSym^.NextOverloaded;
            end;
          ObjDef := ObjDef^.Ancestor;
        end;
    end;

  begin
    FuncSym := nil;
    FuncColl := nil;
    pColl := @FuncColl;
    if Assigned( SymbolTable) then
      begin
        FuncSym := SymbolTable^.Search( FuncName);
        if Assigned( FuncSym) then
          begin
            if FuncSym^._Type in [cFunctionSymbol, cOperatorSymbol] then
              while Assigned( FuncSym) do
                begin
                  if IsCompatible( FuncSym^.Definition^.ParamColl, ParamColl) then
                    begin
                      New( pColl^);
                      pColl^^.Func := FuncSym;
                      pColl^^.Next := nil;
                      pColl^^.Level := 0;
                      pColl := @pColl^^.Next;
                    end;
                  FuncSym := FuncSym^.NextOverloaded;
                end;
          end;
      end
    else if not Assigned( ObjectCode) then
      begin
        STStack := SymTableStack;
        while Assigned( STStack) do
          begin
            if STStack^.Definition^.DefType = cObjectDefinition then
              ScanObjectMethods( pObjectDefinition( STStack^.Definition),
                STStack^.Level );
            STStack := STStack^.Next;
          end;

        if Assigned( CurrentObject) then
          ScanObjectMethods( CurrentObject, -1);

        FuncStack := CurrentFunction;
        while Assigned( FuncStack) do
          begin
            CurTable := FuncStack^.Func^.Definition^.LocalSymbols;
            if Assigned( CurTable) then
              begin
                FuncSym := CurTable^.Search( FuncName);
                if Assigned( FuncSym) then
                  begin
                    if FuncSym^._Type in [cFunctionSymbol, cOperatorSymbol] then
                      while Assigned( FuncSym) do
                        begin
                          if IsCompatible( FuncSym^.Definition^.ParamColl, ParamColl) then
                            begin
                              New( pColl^);
                              pColl^^.Func := FuncSym;
                              pColl^^.Next := nil;
                              pColl^^.Level := 0;
                              pColl := @pColl^^.Next;
                            end;
                          FuncSym := FuncSym^.NextOverloaded;
                        end;
                  end;
              end;
            FuncStack := FuncStack^.Next;
          end;
        if Assigned( UnitSymbol) then
          begin
          FuncSym := UnitSymbol^.UnitSymbols^.Search( FuncName);
          if Assigned( FuncSym) then
            begin
              if FuncSym^._Type in [cFunctionSymbol, cOperatorSymbol] then
                while Assigned( FuncSym) do
                  begin
                    if IsCompatible( FuncSym^.Definition^.ParamColl, ParamColl) then
                      begin
                        New( pColl^);
                        pColl^^.Func := FuncSym;
                        pColl^^.Next := nil;
                        pColl^^.Level := 0;
                        pColl := @pColl^^.Next;
                      end;
                    FuncSym := FuncSym^.NextOverloaded;
                  end;
            end;
          end;
        for Pos := GlobalSymbols^.Count - 1 downto 0 do
          begin
            Sym := pUnitSymbol( GlobalSymbols^.At(Pos));
            if Sym^._Type = cUnitSymbol then
              begin
              FuncSym := Sym^.UnitSymbols^.Search( FuncName);
              if Assigned( FuncSym) then
                begin
                  if FuncSym^._Type in [cFunctionSymbol, cOperatorSymbol] then
                    while Assigned( FuncSym) do
                      begin
                        if IsCompatible( FuncSym^.Definition^.ParamColl, ParamColl) then
                          begin
                            New( pColl^);
                            pColl^^.Func := FuncSym;
                            pColl^^.Next := nil;
                            pColl^^.Level := 0;
                            pColl := @pColl^^.Next;
                          end;
                        FuncSym := FuncSym^.NextOverloaded;
                      end;
                end;
              end;
          end;
      end
    else
      begin
        ScanObjectMethods( pObjectDefinition( ObjectCode^.ResType), -2);
      end;
    FuncSym := nil;
    if Assigned( FuncColl) then
    if not Assigned( FuncColl^.Next) then
      begin
        FuncSym := FuncColl^.Func;
        Level := FuncColl^.Level;
      end
    else
      begin
        Coll := FuncColl;
        while Assigned( Coll) do
          begin
            if IsSameParams( Coll^.Func^.Definition^.ParamColl, ParamColl) then
              if not Assigned( FuncSym) then
                begin
                  FuncSym := Coll^.Func;
                  Level := Coll^.Level;
                  break;
                end;
            Coll := Coll^.Next;
          end;
        if not Assigned( FuncSym) then
          begin
            Coll := FuncColl;
            while Assigned( Coll) do
              begin
                if IsEqualParams( Coll^.Func^.Definition^.ParamColl, ParamColl) then
                  if Assigned( FuncSym) then
                    begin
                      if FuncSym^.Owner <> Coll^.Func^.Owner then
                        break
                      else
                        begin
                          FuncSym := nil;
                          DisposeFunctionStack( FuncColl);
                          Exit;
                        end;
                    end
                  else
                    begin
                      FuncSym := Coll^.Func;
                      Level := Coll^.Level;
                    end;
                Coll := Coll^.Next;
              end;
            if not Assigned( FuncSym) then
              begin
                if FuncColl^.Func^.Owner <> FuncColl^.Next^.Func^.Owner then
                  begin
                    FuncSym := FuncColl^.Func;
                    Level := FuncColl^.Level;
                  end;
              end;
          end;
      end;
    DisposeFunctionStack( FuncColl);
    FindFunction := FuncSym;
  end;


procedure tScanner.OptomizeExpression( var Code: pCodeTree);
  var
    Optomizer: tOptomizer;
  begin
    Optomizer.Init( @Self);
    Optomizer.DoExpression( Code);
    Optomizer.Done;
  end;


procedure tScanner.WriteFunctions( SymbolTable: pSymbolTable; S: pStream);
  var
    I: tIndex;

  procedure WriteAllFunctions( SymbolTable: pSymbolTable); {$IFDEF TP}far;{$ENDIF} forward;

  procedure PutFunction( P: pSymbol); {$IFDEF TP}far;{$ENDIF}
    begin
      if Assigned(P) then
        case P^._Type of
          cFunctionSymbol, cOperatorSymbol:
            begin
              WriteAllFunctions( pFunctionSymbol(P)^.Definition^.LocalSymbols);
              P^.WriteTo( S);
            end;
          cTypeSymbol:
            if pTypeSymbol( P)^.Definition^.DefType = cObjectDefinition then
              begin
                WriteAllFunctions(
                  pObjectDefinition( pTypeSymbol( P)^.Definition)^.PublicSymbols);
              end;
        end;
    end;

  procedure WriteAllFunctions( SymbolTable: pSymbolTable);
    var
      I: tIndex;
    begin
      For I := 0 to SymbolTable^.Count - 1 do
        PutFunction( pSymbol(SymbolTable^.At(I)) );
    end;

  begin
    {For I := 0 to SymbolTable^.Count - 1 do
      PutFunctions( pSymbol(SymbolTable^.At(I)) );}
    if Assigned( MainFunc) then
      PutFunction( MainFunc)
    else
      WriteAllFunctions( GlobalSymbols);
  end;

procedure tScanner.WriteAsmFile;
  const
    {Header: String[27] = '.386p'#13#10+
                     '.MODEL FLAT'#13#10+
                     '.CODE'#13#10;}
    {TypedConstSeg: String[7] = '.DATA'#13#10;
    VariableSeg: String[8] = '.DATA?'#13#10;}
    {StackSeg: String [7] = '.STACK ';}
    LastProgLine: String[10] = 'end ';
    {ExtrnTerminate: String[23] = 'EXTRN terminate: NEAR'#13#10;}
  var
    Str: String;
    AsmFile: pStream;

  procedure PutVariables( P: pSymbol); {$IFDEF TP}far;{$ENDIF}
    begin
      if Assigned(P) and ( P^._Type in [cVariableSymbol]) then
        P^.WriteTo( AsmFile);
    end;

  procedure PutTypedConsts( P: pSymbol); {$IFDEF TP}far;{$ENDIF}
    begin
      if Assigned(P) and ( P^._Type in [cTypedConstSymbol]) then
        begin
          P^.WriteTo( AsmFile);
          {P^.Owner^.Free( @Self);}
        end;
    end;

  procedure DisposeTypedConsts( SymbolTable: pSymbolTable);
    var
      I: Integer;
      P: pSymbol;
    begin
      for I := SymbolTable^.Count - 1 downto 0 do
        begin
          P := SymbolTable^.At( I);
          case P^._Type of
            cTypedConstSymbol:
              pTypedConstSymbol( P)^.DisposeValue;
            {cConstSymbol:
              SymbolTable^.AtFree( I);}
          end;
        end;
    end;

    procedure PutVMT( Sym: pTypeSymbol); {$IFDEF TP}far;{$ENDIF}
      var
        Def: pObjectDefinition;
      begin
        if Sym^._Type = cTypeSymbol then
          begin
            Def := pObjectDefinition( Sym^.Definition);
            if Def^.DefType = cObjectDefinition then
              Def^.WriteVMT( AsmFile);
          end;
      end;

    procedure WritePublic( S: pStream);
      var
        I, J, Pos: Integer;
        HeadStr: String[15];
        Str: String;
        UI: pUnitItem;
        Sym: pSymbol;
        ExternString: String [15];
        PublicString: String [15];
        NearString: String[ 15];
        ByteString: String[ 15];
      begin
        ExternString := AsmSection^.GetValue( ExternKey);
        PublicString := AsmSection^.GetValue( PublicKey);
        NearString := AsmSection^.GetValue( NearKey);
        ByteString := AsmSection^.GetValue( ByteKey);
        if Assigned( UnitCollection) then
          for I := 0 to UnitCollection^.Count - 1 do
            begin
              UI := pUnitItem(UnitCollection^.At(I));
              if Assigned( UnitSymbol) and
                (UI^.UnitName^ =
                UnitSymbol^.SymbolName^) then
                HeadStr := PublicString
              else
                HeadStr := ExternString;
              if not Assigned( UnitSymbol) and Assigned( UI^.SymbolTable) and
                (UI^.SymbolTable^.HasInit) then
                begin
                  Str := HeadStr + ' U_' + UI^.UnitName^ + '$$init'+ NearString + _EOL_;
                  S^.Write( Str[1], Length( Str));
                end;
              for Pos := 0 to UI^.SymbolTable^.Count - 1 do
                begin
                  Sym := UI^.SymbolTable^.At( Pos);
                  if Assigned( Sym) then
                    case Sym^._Type of
                      cFunctionSymbol,
                      cOperatorSymbol,
                      cVariableSymbol,
                      cTypedConstSymbol:
                        if ( (Sym^.Options and csoPublicSymbol <> 0) or
                        ( (Sym^._Type = cFunctionSymbol) and
                        ( Assigned( pFunctionSymbol( Sym)^.Alias) ) ) ) then
                        begin
                          if (Sym^._Type = cFunctionSymbol) and
                            (pFunctionSymbol( Sym)^.Definition^.ProcOptions and poExternal <> 0) then
                            Str := ExternString + ' ' + Sym^.AsmName
                          else  
                            Str := HeadStr + ' ' + Sym^.AsmName;
                          if (Sym^._Type in [cFunctionSymbol,
                            cOperatorSymbol]) then
                            begin
                              if Str[1] = 'E' then
                                Str := Str + NearString;
                              {Sym := pFunctionSymbol( Sym)^.NextOverloaded;}
                            end
                          else
                            begin
                              if Str[1] = 'E' then
                                Str := Str + ByteString;
                              {Sym := nil;}
                            end;
                          Str := Str + _EOL_;
                          S^.Write( Str[1], Length( Str));
                        end;
                      cTypeSymbol:
                        if pTypeSymbol( Sym)^.Definition^.DefType = cObjectDefinition then
                          with pObjectDefinition( pTypeSymbol( Sym)^.Definition)^ do
                            begin
                              with PublicSymbols^ do
                              for J := 0 to Count - 1 do
                                if pSymbol( At( J))^._Type = cFunctionSymbol then
                                  begin
                                    Str := HeadStr + ' '
                                      + pSymbol( At( J))^.AsmName;
                                    if Str[1] = 'E' then
                                      Str := Str + NearString;
                                    Str := Str + _EOL_;
                                    S^.Write( Str[1], Length( Str));
                                  end;
                              Str := HeadStr + ' ' +
                                GetVMTname;
                              if Str[1] = 'E' then
                                Str := Str + NearString;
                              Str := Str + _EOL_;
                              S^.Write( Str[1], Length( Str));
                            end;
                    end;
                end;
            end;
        if not Assigned( UnitSymbol) then
          begin
            for I := 0 to GlobalSymbols^.Count - 1 do
              begin
                Sym := GlobalSymbols^.At( I);
                case Sym^._Type of
                  cFunctionSymbol:
                    if (pFunctionSymbol( Sym)^.Definition^.ProcOptions and poExternal <> 0) then
                      begin
                        Str := ExternString + ' ' + Sym^.AsmName + NearString + _EOL_;
                        S^.Write( Str[ 1], Length( Str));
                      end;
                  cTypeSymbol:
                    if pTypeSymbol( Sym)^.Definition^.DefType = cObjectDefinition then
                      with pObjectDefinition( pTypeSymbol( Sym)^.Definition)^.PublicSymbols^ do
                        begin
                          for J := 0 to Count - 1 do
                            if (pSymbol( At( J))^._Type = cFunctionSymbol) and
                              (pFunctionSymbol( At( J))^.Definition^.ProcOptions and poExternal <> 0) then
                              begin
                                Str := ExternString + ' ' + pSymbol( At( J))^.AsmName + NearString + _EOL_;
                                S^.Write( Str[ 1], Length( Str));
                              end;
                        end;
                end;
              end;
          end;
      end;

  begin
    AsmFile := New( pDosStream, Init( UnitName + AsmExt, stCreate));
    if AsmFile^.Status <> stOK then
      Error( erTooManyOpenFiles, Files^.PrevLine, Files^.PrevCol, '');
    {CurCompiler := @Self;}

    Str := AsmSection^.GetValue( CpuKey) + _EOL_;
    AsmFile^.Write( Str[ 1], Length( Str));
    Str := AsmSection^.GetValue( FpuKey) + _EOL_;
    AsmFile^.Write( Str[ 1], Length( Str));
    Str := AsmSection^.GetValue( ModelKey) + _EOL_;
    AsmFile^.Write( Str[ 1], Length( Str));
    {AsmFile^.Write( Header[1], Length(Header));}

    WritePublic( AsmFile);
    {if not (csCompileSystem in Switches) then
      AsmFile^.Write( ExtrnTerminate[1], Length( ExtrnTerminate));}

    Str := AsmSection^.GetValue( CodeSegmentKey) + _EOL_;
    AsmFile^.Write( Str[ 1], Length( Str));
    WriteFunctions( GlobalSymbols, AsmFile);

    Str := AsmSection^.GetValue( TypedConstSegmentKey) + _EOL_;
    AsmFile^.Write( Str[ 1], Length( Str));
    {AsmFile^.Write( TypedConstSeg[1], Length(TypedConstSeg));}
    GlobalSymbols^.ForEach( @PutTypedConsts);
    DisposeTypedConsts( GlobalSymbols);
    GlobalSymbols^.ForEach( @PutVMT);

    Str := AsmSection^.GetValue( VariableSegmentKey) + _EOL_;
    AsmFile^.Write( Str[ 1], Length( Str));
    {AsmFile^.Write( VariableSeg[1], Length(VariableSeg));}
    GlobalSymbols^.ForEach( @PutVariables);

    if (ResStackSize > 0) and not IsUnit then
      begin
        Str := AsmSection^.GetValue( StackSegmentKey) + ' ' + ToStr( ResStackSize) + _EOL_;
        AsmFile^.Write( Str[1], Length(Str));
      end;

    Str := _End_;
    if not Assigned( UnitSymbol) then
      Str := Str + ' ' + AsmSection^.GetValue( MainKey);
    Str := Str + _EOL_;
    AsmFile^.Write( Str[1], Length(Str));
    Dispose( AsmFile, Done);
  end;


end.
