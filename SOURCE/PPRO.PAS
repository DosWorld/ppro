{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       PPro program                                                    }
{                                              (c) Copyright 1997-1998  }
{                                   Iggor Khachko - hachko@icl.kazan.su }
{-----------------------------------------------------------------------}

program PPro;
{$M 4096, 4096, 4096}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}

uses Dos, Objects, StdLib;

const
  FileListName: String[13] = 'FILELIST';
  AsmFileListName: String[13] = 'ASMLIST';
  CommandParam: String[10] = '/C ';
  CompilerName: String[13] = 'PPROC.EXE';
  Message: String = '';
  AssemblerName: String[13] = 'TASM32.EXE';
  AssemblerParams: String = '/ml /t';
  LinkerName: String[13] = 'TLINK32.EXE';
  LinkerParams: String = '/Tpe /c /Sc:10000 @FILELIST';
  StubItName: String[13] = 'STUBIT.EXE';

function GetCompilerParam: String;
  var
    Param: String;
    I: Integer;
    D: DirStr;
    N: NameStr;
    E: ExtStr;
  begin
    FSplit( ParamStr( 0), D, N, E);
    if D[Length( D)] <> '\' then
      D := D + '\' ;
    Param := CommandParam + D + CompilerName;
    for I := 1 to ParamCount do
      Param := Param + ' ' + ParamStr( I);
    GetCompilerParam := Param;
  end;

function ReadFileName( S: pStream; var Str: String): Boolean;
  var
    C: Char;
  begin
    ReadFileName := False;
    Str := '';
    if Assigned( S) and (S^.Status = stOK) then
      begin
        repeat
          S^.Read( C, SizeOf( C));
        until (C <> ' ') or (S^.Status <> stOK);
        while S^.Status = stOK do
          begin
            C := UpCase( C);
            if C in [#0..#32] then break;
            Str := Str + C;
            S^.Read( C, SizeOf( C));
          end;
        ReadFileName := Str <> '';
      end;
  end;

function GetAssemblerParam( const FileName: String): String;
  var
    Param: String;
  begin
    GetAssemblerParam := CommandParam + ' ' + AssemblerName + ' ' + AssemblerParams + ' ' + FileName;
  end;

function GetLinkerParam: String;
  begin
    GetLinkerParam := CommandParam + ' ' + LinkerName + ' ' + LinkerParams;
  end;

function GetStubParam( const FileName: String): String;
  begin
    GetStubParam := CommandParam + ' ' + StubItName + ' ' + FileName + '.EXE';
  end;

var
  FilesCount: Integer;
  Files: array[ 1..1024] of pString;
  ListFile: pBufStream;
  S: String;
  MainFileName: String;
  Comspec: String;
  I: Integer;

begin
  Write( Message);
  Comspec := GetEnv( 'COMSPEC');
  SwapVectors;
  Exec( Comspec, GetCompilerParam);
  SwapVectors;
  if DosError <> 0 then
    WriteString( 'Ошибка при запуске компилятора.'#13#10);
  if ParamCount < 1 then
    begin
      Halt;
    end;
  if DosExitCode = 0 then
    begin
      Exec( Comspec, '/C BUILD.BAT');
      (*ListFile := New( pBufStream, Init( AsmFileListName, stOpenRead, 1024));
      if ListFile^.Status <> stOK then
        begin
          WriteLn( 'Не удается прочитать список файлов');
          Dispose( ListFile, Done);
        end
      else
        begin
          FilesCount := 0;
          while ListFile^.Status = stOK do
            begin
              if not ReadFileName( ListFile, S) then
                break;
              Inc( FilesCount);
              Files[FilesCount] := NewStr( S);
            end;
          Dispose( ListFile, Done);

          ListFile := New( pBufStream, Init( FileListName, stOpenRead, 1024));
          while ListFile^.Status = stOK do
            begin
              if not ReadFileName( ListFile, S) then
                break;
            end;
          ReadFileName( ListFile, MainFileName);
          Dispose( ListFile, Done);
          if FilesCount = 0 then
            WriteLn( 'Нет файлов для ассемблирования')
          else
            begin
              for I := 1 to FilesCount do
                begin
                  writeln( #9 + AssemblerName + ' ' + AssemblerParams + ' ' + Files[I]^);
                  Exec( Comspec, GetAssemblerParam( Files[I]^ ) );
                  if (DosError <> 0) then
                    begin
                      WriteLn( 'Ошибка при запуске ассемблера.');
                      Halt;
                    end;
                  if DosExitCode <> 0 then
                    Halt;
                end;
              if MainFileName <> '' then
                begin
                  writeln( #9 + LinkerName + ' ' + LinkerParams);
                  Exec( Comspec, GetLinkerParam );
                  if DosError <> 0 then
                    begin
                      WriteLn( 'Ошибка при запуске компоновщика.');
                      Halt;
                   end;
                  if DosExitCode <> 0 then
                    Halt;
                  writeln( #9 + StubItName + ' ' + MainFileName);
                  Exec( Comspec, GetStubParam( MainFileName) );
                  if DosError <> 0 then
                    begin
                      WriteLn( 'Ошибка при запуске FLAT-конвертора.');
                      Halt;
                   end;
                  if DosExitCode <> 0 then
                    Halt;
                end;
            end;
          {EraseFile( FileListName);
          EraseFile( AsmFileListName);}
        end;*)
    end;
end.