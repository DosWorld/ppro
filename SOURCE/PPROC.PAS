{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       Pascal Pro Compiler                                             }
{                                              (c) Copyright 1997-1998  }
{                                   Iggor Khachko - hachko@icl.kazan.su }
{-----------------------------------------------------------------------}

{
  ��� ᮧ�����: 23.08.97
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
          Error('�� ����砥��� ������ 䠩�: '+ ConfFile);
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
          Write('  ���⠪��: PPRO [��樨] ���_䠩�� [��樨]'#13#10);
          Write(#9'��樨:'#13#10);
          Write(#9'  -Sc = ᮮ���� ����������, �� ������������ ����� SYSTEM'#13#10);
          Write(#9'  -U���� = �������� ���� � ᯨ�� ���᪠ ���㫥�'#13#10);
          Write(#9'  -I���� = �������� ���� � ᯨ�� ���᪠ ����砥��� 䠩���'#13#10);
          Write(#9'  -O���� = �������� ���� � ᯨ�� ���᪠ ��ꥪ��� 䠩���'#13#10);
          Write(#9'  -M�� = ��⠭����� �� ��� �뤠������ ��������஬ ᮮ�饭��'#13#10);
          Write(#9#9'eng - ᮮ�饭�� �� ������᪮�'#13#10);
          Write(#9#9'rus - ᮮ�饭�� �� ���᪮�'#13#10);
          Write(#9'  -T�����ଠ = ��।����� ������� ��� ������㥬��� ����'#13#10);
          Write(#9#9'WDOSX - ���᪠� ������ ����� � �ᯮ�짮������ WDOSX-����⥫�'#13#10);
          Write(#9#9'DOS32 - ���᪠� ������ ����� � �ᯮ�짮������ DOS32-����⥫�'#13#10);
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
      Write('Pascal Pro ���������. Copyright (c) 1997-1999 ����� ��窮'#13#10);
        {'������������...'#13#10);}
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
              Write('�����祭�.'#13#10);
              WriteLn( TotalLines, ' ��ப, ',
                (GetTicks - InitTime) / 18.2 : 4: 2, ' ᥪ㭤.');
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