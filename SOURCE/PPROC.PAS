{                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/gpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

{
  Дата создания: 23.08.97
}

{$IFDEF TP}
{$M 65520}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

program PProC;

uses StdLib, Dos, Objects, Config, Compiler, Errors, Symbols, FileColl;

const
  FileName: String = '';
  ConfigFileName: String[14] = 'PPRO.CFG';

procedure InitSearchPath;
  var
    Dir: DirStr;
    N: NameStr;
    E: ExtStr;
  begin
    GetDir(0, Dir);
    AddSearchPath(Dir, UnitSearchPath);
    AddSearchPath(Dir, IncludeSearchPath);
    AddSearchPath(Dir, ProgramSearchPath);
    AddSearchPath(Dir, ObjSearchPath);
    FSplit( FExpand(ParamStr(0)), Dir, N, E);
    AddSearchPath(Dir, UnitSearchPath);
    AddSearchPath(Dir, IncludeSearchPath);
    AddSearchPath(Dir, ProgramSearchPath);
    AddSearchPath(Dir, ObjSearchPath);
  end;

procedure LoadConfigFile(ConfFile: PathStr);
  var
    F: Text;
    S: String;
    Dir: DirStr;
    N: NameStr;
    E: ExtStr;
  begin
    FSplit( ConfFile, Dir, N, E);
    Assign(F, ConfFile);
    {$IFDEF TP}{$I-}{$ENDIF}
    Reset(F);
    if IOResult <> 0
      then
        begin
          Error('Не получается открыть файл: '+ ConfFile);
          Halt(0);
        end;
    while not Eof(F) do
      begin
        ReadLn(F, S);
        if Pos(';', S) <> 0 then S[0] := Char(Pos(';', S));
        AddSwitch(S, Dir);
      end;
    Close(F);
  end;

procedure ReadParamStr;
  var
    S: String;
    I: Integer;
  begin
    if FindFile(ConfigFileName, S, UnitSearchPath) then LoadConfigFile( S);
    for I := 1 to ParamCount do
      begin
        S := ParamStr(I);
        case S[1] of
          '-', '/': AddSwitch(S, '');
          '@': LoadConfigFile( Copy(S, 1, Length(S)));
          else
            if FileName = '' then FileName := S;
        end;
      end;
    if ErrorFile = '' then ErrorFile := DefaultErrorFile;
    if FindFile( ErrorFile, S, ProgramSearchPath) then
      LoadErrorFile( S);
  end;

procedure WriteInformation;
  begin
    case Language of
      clRussian:
        begin
          Write('  Синтаксис: PPRO [опции] имя_файла [опции]'#13#10);
          Write(#9'Опции:'#13#10);
          Write(#9'  -Sc = сообщить компилятору, что компилируется модуль SYSTEM'#13#10);
          Write(#9'  -Uпуть = добавить путь к списку поиска модулей'#13#10);
          Write(#9'  -Iпуть = добавить путь к списку поиска включаемых файлов'#13#10);
          Write(#9'  -Oпуть = добавить путь к списку поиска объектных файлов'#13#10);
          Write(#9'  -Mязык = установить язык для выдаваемых компилятором сообщений'#13#10);
          Write(#9#9'eng - сообщения на английском'#13#10);
          Write(#9#9'rus - сообщения на русском'#13#10);
          Write(#9'  -Tплатформа = определить платформу для генерируемого кода'#13#10);
          Write(#9#9'WDOSX - плоская модель памяти с использованием WDOSX-расширителя'#13#10);
          Write(#9#9'DOS32 - плоская модель памяти с использованием DOS32-расширителя'#13#10);
        end;
      clEnglish:
        begin
          Write('  Syntax: PPRO [options] filename [options]'#13#10);
          Write(#9'Options:'#13#10);
          Write(#9'  -Sc = system unit is compiled'#13#10);
          Write(#9'  -Upath = add path to units search list'#13#10);
          Write(#9'  -Ipath = add path to include files search list'#13#10);
          Write(#9'  -Opath = add path to object files search list'#13#10);
          Write(#9'  -Mlanguage = set language for compiler messages'#13#10);
          Write(#9#9'eng - messages in English'#13#10);
          Write(#9#9'rus - messages in Russian'#13#10);
          Write(#9'  -Tplatform = defines platform for compiler output'#13#10);
          Write(#9#9'WDOSX - flat memory model with WDOSX-extender'#13#10);
          Write(#9#9'DOS32 - flat memory model with DOS32-extender'#13#10);
        end;
    end;
  end;

var
  MemBefore: LongInt;
  InitTime: LongInt;

function GetTicks: LongInt;
  begin
    GetTicks := MemL[
      {$IFDEF TP} $40: $6C {$ENDIF}
      {$IFDEF PPRO} $46C {$ENDIF} ];
  end;

{var
  curdir: string;}

begin
  DefaultMacro := New( pSymbolTable, Init( stMacrosTable, 5, 5));
  InitSearchPath;
  ReadParamStr;
  RegisterObjects;
  RegisterSymbols;
  RegisterType( RFileDateCollection);
  RegisterType( RFileCollection);
  MemBefore := Memavail;
  case Language of
    clRussian:
      Write('Pascal Pro компилятор. Copyright (c) 1997-1999 Игорь Хачко'#13#10);
        {'Компилируется...'#13#10);}
    clEnglish:
       Write('Pascal Pro compiler. Copyright (c) 1997-1999 Iggor Khachko'#13#10);
                  {'Compiling...'#13#10);}
  end;
  if FileName = ''
    then
      WriteInformation
    else
      begin
        InitUnitCollection;
        InitTime := GetTicks;
        BatchFile := New( pBufStream, Init( 'build.bat', stCreate, 1024));
        Compile(FileName);
        Dispose( BatchFile, Done);

        DoneUnitCollection;
        DisposeDefinitions;
        case Language of
          clRussian:
            begin
              Write('Закончено.'#13#10);
              WriteLn( TotalLines, ' строк, ',
                (GetTicks - InitTime) / 18.2 : 4: 2, ' секунд.');
            end;
          clEnglish:
            begin
              Write('Completed.'#13#10);
              WriteLn( TotalLines, ' lines, ',
                (GetTicks - InitTime) / 18.2: 4: 2, ' seconds.');
            end;
       end;
      end;
{$IFDEF DEBUG}
  WriteLn( MemBefore - Memavail);
{$ENDIF}
  Exit;
end.