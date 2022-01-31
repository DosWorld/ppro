{                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/gpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

{
  Дата создания: 23.08.97
  Этот модуль содержит объект, который и занимается такой скушной работой,
  как компиляция.
}

{$IFDEF TP}

{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}

{$ENDIF}

unit Compiler;

interface

uses Dos, Objects, Config, Scanner, PasComp;

procedure Compile( const FileName: PathStr);

const
  CurCompiler: pCompiler = nil;


implementation

uses Errors, Tools;

procedure Compile( const FileName: PathStr);

  var
    PascalCompiler: pCompiler;
    OldCompiler: pCompiler;
    FStream: pBufStream;
    FName: PathStr;
    FN: String[ 14];
    D: DirStr;
    N: NameStr;
    E: ExtStr;
    C: Char;
  begin
    Write('                                                                               '#13);
    FSplit(FileName, D, N, E);
    if E = '' then E := '.PAS';
    FN := N + E;
    if not FindFile(FN, FName, UnitSearchPath) then
      begin
        Error(GetErrorMessage( erFileNotFound) + ' : "' + FileName + '"');
        Halt( erFileNotFound);
      end;
    {WriteLn(FN);}

    OldCompiler := CurCompiler;
    PascalCompiler := New(pCompiler, Init( FName, N));
    CurCompiler := PascalCompiler;
    if PascalCompiler^.LastToken = ctUnit then
      begin
        PascalCompiler^.CompileUnit;
        Dispose(PascalCompiler, Done);
      end
    else
      begin
        ListFile := New(pBufStream, Init( 'FileList', stCreate, 4096));
        PascalCompiler^.CompileProgram;
        Dispose(PascalCompiler, Done);
        Dispose( ListFile, Done);
      end;
    CurCompiler := OldCompiler;
  end;


end.
