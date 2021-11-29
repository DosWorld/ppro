{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       Config unit                                                     }
{                                              (c) Copyright 1997-1998  }
{                                   Iggor Khachko - hachko@icl.kazan.su }
{-----------------------------------------------------------------------}

{
  Дата создания: 23.08.97
}

unit Config;

{$IFDEF TP}

{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}

{$ENDIF}

interface

uses Dos, Objects, Profile;

type

  tSwitch = ( csFarFunctions, csRangeChecking, csIOChecking,
    csStrictStrings, csCompileSystem);
  tSwitches = set of tSwitch;

  tLanguage = ( clRussian, clEnglish );

  tPlatform = record
    Name: String[63];
    _Assembler: PathStr;
    AsmSwitches: String;
    Linker: PathStr;
    LinkSwitches: String;
    Stub: PathStr;
    UnitExt: ExtStr;
    AsmExt: ExtStr;
    ObjExt: ExtStr;
  end;

  {tPlatformType = ( cpWDOSX, cpDOS32 );}

const

  DefaultSwitches: tSwitches = [csStrictStrings];
  Language: tLanguage = clRussian;
  TotalLines: LongInt = 0;

  StackSize: LongInt = 32768;

  TargetKey = 'TARGET';

  AssemblerKey = 'ASSEMBLER';
  AssemblerOptionsKey = 'ASSEMBLEROPTIONS';
  LinkerKey = 'LINKER';
  LinkerOptionsKey = 'LINKEROPTIONS';
  StuberKey = 'STUBER';
  StuberOptionsKey = 'STUBEROPTIONS';
  UnitExtKey = 'UNITEXTENSION';
  ObjExtKey = 'OBJEXTENSION';
  AsmExtKey = 'ASMEXTENSION';
  ReserveStackKey = 'RESERVESTACKSIZE';
  SeparateKey = 'SEPARATEBYEOL';

  cAsmFile = '$asmfile$';
  cObjFile = '$objfile$';
  cExeFile = '$exefile$';
  cStackCommitSize = '$stackcommitsize$';

  CpuKey                = 'CPU';
  FpuKey                = 'FPU';
  ModelKey              = 'MODEL';
  ExternKey             = 'EXTRN';
  PublicKey             = 'PUBLIC';
  NearKey               = 'NEAR';
  ByteKey               = 'BYTE';
  CodeSegmentKey        = 'CODE';
  TypedConstSegmentKey  = 'DATA';
  StackSegmentKey       = 'STACK';
  VariableSegmentKey    = 'DATA_';
  MainKey               = 'MAIN';
  EndKey                = 'END';
  ProcKey               = 'PROC';
  EndPKey               = 'ENDP';
  DBKey                 = 'DB';
  DWKey                 = 'DW';
  DDKey                 = 'DD';
  DQKey                 = 'DQ';
  DTKey                 = 'DT';
  DupKey                = 'DUP';
  ResBKey               = 'RESB';
  StKey                 = 'ST';
  BPtrKey               = 'BPTR';
  WPtrKey               = 'WPTR';
  DPtrKey               = 'DPTR';
  QPtrKey               = 'QPTR';
  TPtrKey               = 'TPTR';
  FPtrKey               = 'FPTR';
  NPtrKey               = 'NPTR';
  PPtrKey               = 'PPTR';
  OffsetKey             = 'OFFSET';
  StartKey              = 'START';

  ExtFloatKey           = 'EXTENDEDFLOATINSTRUCTIONS';
  NasmPushKey           = 'NASMPUSHCONST';
  NasmSegOverrideKey    = 'NASMSEGMENTOVERRIDE';

  {Platforms: array [tPlatformType] of tPlatform =
  (
    (
      Name: 'WDOSX';
      _Assembler: 'TASM32.EXE';
      AsmSwitches: '/ml /t';
      Linker: 'TLINK32.EXE';
      LinkSwitches: '/Tpe /c /Sc:10000 @FILELIST';
      Stub: 'STUBIT.EXE';
      UnitExt: '.PU';
      AsmExt: '.ASM';
      ObjExt: '.OBJ'
    ),

    (
      Name: 'DOS32';
      _Assembler: 'TASM32.EXE';
      AsmSwitches: '/ml /t';
      Linker: 'DLINK.EXE';
      LinkSwitches: '/c @FILELIST';
      Stub: '';
      UnitExt: '.PUD';
      AsmExt: '.ASM';
      ObjExt: '.OBD'
    )
  );}

  IniFileName: String = 'PPRO.SRC';

  TargetName: String = 'WDOSX';
  UnitExt: PathStr = '.PU';
  AsmExt: String[4] = '.ASM';
  ObjExt: String[4] = '.OBJ';
  BinExt: String[4] = '.BIN';
  ExeExt: String[4] = '.EXE';

  {Platform: tPlatformType = cpWDOSX;}

  AsmCompiler: PathStr = 'TASM32';
  AsmSwitches: String = '/ml /t ' + cAsmFile + ', ' + cObjFile;
  Linker: PathStr = 'TLINK32';
  LinkerSwitches: String = '/Tpe /c /Sc:' + cStackCommitSize + ' @FILELIST, ' + cExeFile;
  Stuber: PathStr = 'STUBIT';
  StuberOptions: String = cExeFile;
  ResStackSize: LongInt = 0;
  StackCommitSize: LongInt = 65536;
  AsmSection: pKeyCollection = nil;
  SeparateByEOL: Boolean = False;

  LoaderName: PathStr = 'PESTUB.EXE';

  ListFile: pStream = nil;
  BatchFile: pStream = nil;

  SystemUnitName: String[8] = 'SYSTEM';

  ErrorFile: String = '';
  ErrorFileName = 'ERRORS';
  DefaultErrorFile = ErrorFileName + '.RUS';

  _DB_: String[7] = 'DB';
  _DW_: String[7] = 'DW';
  _DD_: String[7] = 'DD';
  _DQ_: String[7] = 'DQ';
  _DT_: String[7] = 'DT';
  _DUP_: String[7] = 'DUP(?)';
  _ResB_: String[7] = 'DB';
  _FpuReg_: String[ 7] = 'ST(#)';
  _Proc_: String[ 7] = 'PROC';
  _EndP_: String[ 7] = 'ENDP';
  _End_: String[ 7] = 'END';
  _Offset_: String[ 7] = 'offset';
  _Start_: String[ 15] = '';

  ExtFloat: Boolean = True;
  NasmPush: Boolean = False;
  NasmSegOverride: Boolean = False;

function FindFile( const FName: PathStr; var Dst: PathStr; SearchPath: PChar): Boolean;

procedure AddSearchPath( const SPath: DirStr; var SearchPath: PChar);

procedure AddSwitch( const Sw: String; const Dir: DirStr);

function GetLoaderName: String;

function CreateAsmParam( const FileName: PathStr): String;

function CreateLinkerParam( const FileName: PathStr): String;

function CreateStuberParam( const FileName: PathStr): String;

const
  UnitSearchPath: PChar = Nil;
  ObjSearchPath: PChar = Nil;
  IncludeSearchPath: PChar = Nil;
  ProgramSearchPath: PChar = Nil;

implementation

uses Strings, StdLib, Symbols, IAsm386;

type
  pCharArray = ^tCharArray;
  tCharArray = array [0..6520] of char;

function IsTrue( const S: String): Boolean;
  begin
    IsTrue := (S = 'YES') or (S = 'ON') or (S = 'TRUE');
  end;

procedure AddSwitch( const Sw: String; const Dir: DirStr);
  var
    Path: PathStr;
    {PT: tPlatformType;}
    B: Boolean;
    Section: String;
    S: String;
    P: pKeyCollection;
    L: LongInt;
    Res: Integer;
  begin
{writeln( 'ADDSwitch: ', Sw);}
    if Length( Sw) < 2 then exit;
    case Sw[2] of
      'C':
        if Copy( Sw, 2, 255) = 'Cs' then
          DefaultSwitches := DefaultSwitches + [csCompileSystem];
      'U':
        begin
          Path := Copy( Sw, 3, 255);
          if Copy( Path, 1, 2) = '..' then
            begin
              Path := Dir + Path;
              FExpand( Path);
            end;
          AddSearchPath( Path, UnitSearchPath);
        end;
      'I':
        begin
          Path := Copy( Sw, 3, 255);
          if Copy( Path, 1, 2) = '..' then
            begin
              Path := Dir + Path;
              FExpand( Path);
            end;
          AddSearchPath( Path, IncludeSearchPath);
        end;
      'O':
        begin
          Path := Copy( Sw, 3, 255);
          if Copy( Path, 1, 2) = '..' then
            begin
              Path := Dir + Path;
              FExpand( Path);
            end;
          AddSearchPath( Path, ObjSearchPath);
        end;
      'M':
        if ErrorFile = '' then
          begin
            Path := Copy( Sw, 3, 3);
            if Sw = 'rus' then
              begin
                ErrorFile := ErrorFileName + '.RUS';
                Language := clRussian;
              end
            else if Path = 'eng' then
              begin
                ErrorFile := ErrorFileName + '.ENG';
                Language := clEnglish;
              end;
          end;
      'T':
        begin
          Section := UpStr( Copy( Sw, 3, 63));
          if FindFile( IniFileName, Path, ProgramSearchPath) and
            SectionExists( Path, Section) then
            begin
              TargetName := Section;
              S := GetPrivateProfileString( Path, Section, AssemblerKey);
              if S <> '' then AsmCompiler := S;
              AsmSwitches := GetPrivateProfileString( Path, Section, AssemblerOptionsKey);
              S := GetPrivateProfileString( Path, Section, LinkerKey);
              if S <> '' then Linker := S;
              LinkerSwitches := GetPrivateProfileString( Path, Section, LinkerOptionsKey);
              Stuber := GetPrivateProfileString( Path, Section, StuberKey);
              StuberOptions := GetPrivateProfileString( Path, Section, StuberOptionsKey);
              UnitExt := GetPrivateProfileString( Path, Section, UnitExtKey);
              ObjExt := GetPrivateProfileString( Path, Section, ObjExtKey);
              AsmExt := GetPrivateProfileString( Path, Section, AsmExtKey);
              SeparateByEOL := IsTrue( GetPrivateProfileString( Path, Section, SeparateKey));
              ResStackSize := 0;
              S := GetPrivateProfileString( Path, Section, ReserveStackKey);
              if S <> '' then
                begin
                  Val( S, L, Res);
                  if Res = 0 then
                    ResStackSize := L;
                end;
              P := ReadSection( Path, ExtractFileName( AsmCompiler) );
              if Assigned( P) then
                begin
                  if Assigned( AsmSection) then
                    Dispose( AsmSection, Done);
                  AsmSection := P;
                  ExtFloat := IsTrue( AsmSection^.GetValue( ExtFloatKey));
                  NasmPush := IsTrue( AsmSection^.GetValue( NasmPushKey));
                  NasmSegOverride := IsTrue( AsmSection^.GetValue( NasmSegOverrideKey));
                  _DB_ := AsmSection^.GetValue( DBKey);
                  _DW_ := AsmSection^.GetValue( DWKey);
                  _DD_ := AsmSection^.GetValue( DDKey);
                  _DQ_ := AsmSection^.GetValue( DQKey);
                  _DT_ := AsmSection^.GetValue( DTKey);
                  _DUP_ := AsmSection^.GetValue( DupKey);
                  _ResB_ := AsmSection^.GetValue( ResBKey);
                  _FpuReg_ := AsmSection^.GetValue( StKey);
                  _Ptr[ csByte] := AsmSection^.GetValue( BPtrKey);
                  _Ptr[ csWord] := AsmSection^.GetValue( WPtrKey);
                  _Ptr[ csDWord] := AsmSection^.GetValue( DPtrKey);
                  _Ptr[ csQWord] := AsmSection^.GetValue( QPtrKey);
                  _Ptr[ csTByte] := AsmSection^.GetValue( TPtrKey);
                  _Ptr[ csNear] := AsmSection^.GetValue( NPtrKey);
                  _Ptr[ csFar] := AsmSection^.GetValue( FPtrKey);
                  _Ptr[ csPWord] := AsmSection^.GetValue( PPtrKey);
                  _Offset_ := AsmSection^.GetValue( OffsetKey);
                  _Proc_ := AsmSection^.GetValue( ProcKey);
                  _EndP_ := AsmSection^.GetValue( EndPKey);
                  _End_ := AsmSection^.GetValue( EndKey);
                  _Start_ := AsmSection^.GetValue( StartKey);
                end;
            end
          else {...};
        end;
      'D':
        begin
          DefaultMacro^.Insert( New( pMacroSymbol, Init( UpStr( Copy( Sw, 3, 63)))));
        end;
    end;
  end;

function FindFile( const FName: PathStr; var Dst: PathStr; SearchPath: PChar): Boolean;

  function Scan( S: PChar; C: Char): Word; Assembler;
    asm
{$IFDEF TP}
      les  di, s
      mov  al, c
      xor  cx, cx
    @@1:
      mov ah, es:[di]
      or  ah, ah
      je  @@2
      cmp ah, al
      je  @@2
      inc cx
      inc di
      jmp @@1
    @@2:
      mov ax, cx
{$ENDIF}
{$IFDEF PPRO}
      mov  edi, s
      mov  al, c
      xor  ecx, ecx
    @@1:
      mov ah, byte ptr [edi]
      or  ah, ah
      je  @@2
      cmp ah, al
      je  @@2
      inc ecx
      inc edi
      jmp @@1
    @@2:
      mov eax, ecx
{$ENDIF}
    end;

  var
    P: PChar;
    S: PathStr;
    W: Word;
  begin
    {Dst := '';}
    if SearchPath = Nil
      then FindFile := False
      else
        begin
          P := SearchPath;
          W := 0;
          while StrLen(P) > 0 do
            begin
              W := Scan(P, ';');
              if pCharArray( P)^[W] = ';' then
                begin
                  Move( P^, S[1], W);
                  S[0] := Char(W);
                  if S[Length(S)] <> '\' then S := S + '\';
                  S := S + FName;
                  if FExists(S) then
                    begin
                      Dst := S;
                      FindFile := True;
                      Exit;
                    end;
                end;
              P := @pCharArray( P)^[W + 1];
            end;
        end;
    FindFile := False;
  end;

procedure AddSearchPath( const SPath: DirStr; var SearchPath: PChar);
  var
    P: PChar;
    S: DirStr;
  begin
    S := SPath;
    if S[Byte(S[0])] <> ';' then S := S + ';';
    if SearchPath = Nil
       then
         begin
           GetMem(P, Length(S) + 1);
           pCharArray(P)^[0] := #0;
         end
       else
         begin
           GetMem(P, StrLen( SearchPath) + Length(S) + 1);
           StrCopy(P, SearchPath);
           StrDispose( SearchPath);
         end;
    StrPCopy( @(pCharArray(P)^[StrLen(P)]), S);
    SearchPath := P;
  end;


function GetLoaderName: String;
  var
    ResStr: String;
  begin
    if not FindFile( LoaderName, ResStr, ProgramSearchPath) then
      ResStr := '';
    GetLoaderName := ResStr;
  end;


function CreateAsmParam( const FileName: PathStr): String;
  var
    Res: String;
    L: LongInt;
  begin
    Res := AsmSwitches;
    L := Pos( cAsmFile, Res);
    if L > 0 then
      Res := Copy( Res, 1, L - 1) + FileName + AsmExt + Copy( Res, L + Length( cAsmFile), 255);
    L := Pos( cObjFile, Res);
    if L > 0 then
      Res := Copy( Res, 1, L - 1) + FileName + ObjExt + Copy( Res, L + Length( cObjFile), 255);
    CreateAsmParam := Res;
  end;


function CreateLinkerParam( const FileName: PathStr): String;
  var
    Res: String;
    L: LongInt;
  begin
    Res := LinkerSwitches;
    L := Pos( cExeFile, Res);
    if L > 0 then
      Res := Copy( Res, 1, L - 1) + FileName + ExeExt + Copy( Res, L + Length( cExeFile), 255);
    L := Pos( cStackCommitSize, Res);
    if L > 0 then
      Res := Copy( Res, 1, L - 1) + ToStr( StackCommitSize) + Copy( Res, L + Length( cStackCommitSize), 255);
    CreateLinkerParam := Res;
  end;


function CreateStuberParam( const FileName: PathStr): String;
  var
    Res: String;
    L: LongInt;
  begin
    Res := StuberOptions;
    L := Pos( cExeFile, Res);
    if L > 0 then
      Res := Copy( Res, 1, L - 1) + FileName + ExeExt + Copy( Res, L + Length( cExeFile), 255);
    CreateStuberParam := Res;
  end;


end.
