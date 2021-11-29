{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       Tools unit                                                      }
{                                              (c) Copyright 1997-1998  }
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

unit Tools;

interface

uses Dos, Objects, UnitStrm, Symbols, Code, IAsm386;

type

  tToken = (
    ctPlus,             { '+' }
    ctMinus,            { '-' }
    ctStar,             { '*' }
    ctSlash,            { '/' }
    ctEqual,            { '=' }
    ctGreater,          { '>' }
    ctLess,             { '<' }
    ctLParen,           { '(' }
    ctRParen,           { ')' }
    ctLBracket,         { '[' }
    ctRBracket,         { ']' }
    ctPoint,            { '.' }
    ctComma,            { ',' }
    ctColon,            { ':' }
    ctSemiColon,        { ';' }
    ctCarret,           { '^' }
    ctAt,               { '@' }
    ctAssignment,       { ':=' }
    ctUnequal,          { '<>' }
    ctGreaterEq,        { '>=' }
    ctLessEq,           { '<=' }
    ctPointPoint,       { '..' }
    ctIdentifier,       { '' }
    ctRealConst,        { '' }
    ctEof,              { 'END.' }
    ctIntConst,         { '' }
    ctStringConst,      { '' }
    ctCharConst,        { '' }

    ctAbsolute,         { 'absolute' }
    ctAnd,              { 'and' }
    ctArray,            { 'array' }
    ctAsm,              { 'asm' }
    ctAssembler,        { 'assembler' }
    ctBegin,            { 'begin' }
    ctBreak,            { 'break' }
    ctCase,             { '' }
    ctCdecl,            { '' }
    ctConst,            { '' }
    ctConstructor,      { '' }
    ctContinue,         { '' }
    ctDestructor,       { '' }
    ctDispose,          { '' }
    ctDiv,              { '' }
    ctDo,               { '' }
    ctDownTo,           { '' }
    ctElse,             { '' }
    ctEnd,              { '' }
    ctExit,             { '' }
    ctExternal,         { '' }
    ctFalse,            { '' }
    ctFar,              { '' }
    ctFile,             { '' }
    ctFor,              { '' }
    ctForward,          { '' }
    ctFunction,         { '' }
    ctGoto,             { '' }
    ctIf,               { '' }
    ctImplementation,   { '' }
    ctIn,               { '' }
    ctInherited,        { '' }
    ctInline,           { '' }
    ctInterface,        { '' }
    ctInterrupt,        { '' }
    ctLabel,            { '' }
    ctMod,              { '' }
    ctNear,             { '' }
    ctNew,              { '' }
    ctNil,              { '' }
    ctNot,              { '' }
    ctObject,           { '' }
    ctOf,               { '' }
    ctOr,               { '' }
    ctPacked,           { '' }
    ctPascal,           { '' }
    ctPrivate,          { '' }
    ctProcedure,        { '' }
    ctProgram,          { '' }
    ctProtected,        { '' }
    ctPublic,           { '' }
    ctRecord,           { '' }
    ctRepeat,           { '' }
{    ctSelf, }            { '' }
    ctSet,              { '' }
    ctShl,              { '' }
    ctShr,              { '' }
    ctStdcall,          { '' }
    ctString,           { '' }
    ctThen,             { '' }
    ctTo,               { '' }
    ctTrue,             { '' }
    ctType,             { '' }
    ctUnit,             { '' }
    ctUntil,            { '' }
    ctUses,             { '' }
    ctVar,              { '' }
    ctVirtual,          { '' }
    ctWhile,            { '' }
    ctWith,             { '' }
    ctXor,

    ctClass,            { 'class' }

    ctOperator,         { 'operator' }

    ctPlusAsn,          { '+=' }
    ctMinusAsn,         { '-=' }
    ctAndAsn,           { 'and=' }
    ctOrAsn,            { 'or=' }
    ctStarAsn,          { '*=' }
    ctSlashAsn,         { '\=' }
    ctModAsn,           { 'mod=' }
    ctDivAsn,           { 'div=' }
    ctShlAsn,           { 'shl=' }
    ctShrAsn,           { 'shr=' }
    ctXorAsn            { 'xor=' }

    {ctAsmCommand,
    ctRegister}
  );

  tOperators = (
    coPlus,
    coMinus,
    coStar,
    coDiv,
    coMod,
    coSlash,
    coGreater,
    coLess,
    coGreaterEq,
    coLessEq,
    coEqual,
    coUnequal,
    coAssignment,
    coNew,
    coDispose,
    coIndexInArray,
    coAnd,
    coOr,
    coNot,
    coXor,
    coShl,
    coShr,
    coPlusAsn,
    coMinusAsn,
    coStarAsn,
    coSlashAsn,
    coDivAsn,
    coModAsn,
    coAndAsn,
    coOrAsn,
    coXorAsn,
    coShlAsn,
    coShrAsn
  );

const

  OperatorAssignment :set of tToken =
  [ ctPlus, ctMinus, ctStar, ctSlash, ctDiv, ctMod, ctAnd, ctOr, ctXor,
    ctShl, ctShr];

  KeyWordsCount = Ord( ctOperator) - Ord( ctAbsolute) + 1;

  KeyWordsToken: array [0..KeywordsCount - 1] of tToken =
  (
    ctAbsolute,
    ctAnd,
    ctArray,
    ctAsm,
    ctAssembler,
    ctBegin,
    ctBreak,
    ctCase,
    ctCDECL,
    ctClass,
    ctConst,
    ctConstructor,
    ctContinue,
    ctDestructor,
    ctDispose,
    ctDiv,
    ctDo,
    ctDOWNTO,
    ctELSE,
    ctEND,
    ctEXIT,
    ctEXTERNAL,
    ctFALSE,
    ctFAR,
    ctFILE,
    ctFOR,
    ctFORWARD,
    ctFUNCTION,
    ctGOTO,
    ctIF,
    ctIMPLEMENTATION,
    ctIN,
    ctINHERITED,
    ctINLINE,
    ctINTERFACE,
    ctINTERRUPT,
    ctLABEL,
    ctMOD,
    ctNEAR,
    ctNEW,
    ctNIL,
    ctNOT,
    ctOBJECT,
    ctOF,
    ctOPERATOR,
    ctOR,
    ctPACKED,
    ctPASCAL,
    ctPRIVATE,
    ctPROCEDURE,
    ctPROGRAM,
    ctPROTECTED,
    ctPUBLIC,
    ctRECORD,
    ctREPEAT,
    {ctSELF,}
    ctSET,
    ctSHL,
    ctSHR,
    ctSTDCALL,
    ctSTRING,
    ctTHEN,
    ctTO,
    ctTRUE,
    ctTYPE,
    ctUNIT,
    ctUNTIL,
    ctUSES,
    ctVAR,
    ctVIRTUAL,
    ctWHILE,
    ctWITH,
    ctXOR
  );

  KeyWords: array [0..KeywordsCount - 1] of string[14] =
  (
    'ABSOLUTE',
    'AND',
    'ARRAY',
    'ASM',
    'ASSEMBLER',
    'BEGIN',
    'BREAK',
    'CASE',
    'CDECL',
    'CLASS',
    'CONST',
    'CONSTRUCTOR',
    'CONTINUE',
    'DESTRUCTOR',
    'DISPOSE',
    'DIV',
    'DO',
    'DOWNTO',
    'ELSE',
    'END',
    'EXIT',
    'EXTERNAL',
    'FALSE',
    'FAR',
    'FILE',
    'FOR',
    'FORWARD',
    'FUNCTION',
    'GOTO',
    'IF',
    'IMPLEMENTATION',
    'IN',
    'INHERITED',
    'INLINE',
    'INTERFACE',
    'INTERRUPT',
    'LABEL',
    'MOD',
    'NEAR',
    'NEW',
    'NIL',
    'NOT',
    'OBJECT',
    'OF',
    'OPERATOR',
    'OR',
    'PACKED',
    'PASCAL',
    'PRIVATE',
    'PROCEDURE',
    'PROGRAM',
    'PROTECTED',
    'PUBLIC',
    'RECORD',
    'REPEAT',
    {'SELF',}
    'SET',
    'SHL',
    'SHR',
    'STDCALL',
    'STRING',
    'THEN',
    'TO',
    'TRUE',
    'TYPE',
    'UNIT',
    'UNTIL',
    'USES',
    'VAR',
    'VIRTUAL',
    'WHILE',
    'WITH',
    'XOR'
  );

type

  pFunctionStack = ^tFunctionStack;
  tFunctionStack = record
    Func: pFunctionSymbol;
    Level: LongInt;
    Next: pFunctionStack;
  end;

  pSymbolTableStack = ^tSymbolTableStack;
  tSymbolTableStack = record
    Definition: pDefinition;
    Level: LongInt;
    Next: pSymbolTableStack;
  end;


function IsConst( Code: pCodeTree): Boolean;
function GetParamType( CodeTree: pCodeTree): tVariableType;
procedure DisposeFunctionStack( FuncStack: pFunctionStack);
function GetOperatorType( Token: tToken): tPasOperators;

function GetBaseType( Min, Max: LongInt): tBaseType;

function GetSize( Size: LongInt): tSize;
function GetReg( Reg: tRegister; Size: tSize): tRegister;
function GetRegL( Reg: tRegister): tRegister;
function GetRegH( Reg: tRegister): tRegister;
function GetEAX( Size: tSize): tRegister;
function GetEBX( Size: tSize): tRegister;
function GetECX( Size: tSize): tRegister;
function GetEDX( Size: tSize): tRegister;

function CreatePointerValue( CodeTree: pCodeTree): pPointerValue;

function ReverseDefColl( DefColl: pDefCollection): pDefCollection;

function _LEA_( Register: tRegister; Reference: tReference): pAsmInstruction;
function _PUSH_( Register: tRegister): pAsmInstruction;
function _PUSH_const( Value: LongInt): pAsmInstruction;
function _POP_( Register: tRegister): pAsmInstruction;

const
  cluNormal             = 0;
  cluUnitRecompiled     = 1;

function LoadUnitFile( const aUnitName, aFileName: String): Integer;

function EqualHeaders( Func1, Func2: pFunctionSymbol): Boolean;

function IsAncestor( ODef1, ODef2: pObjectDefinition): Boolean;

function GetUnitTable( Symbol: pSymbol): pSymbolTable;

procedure DisposeValue( var Value: tValue; Def: pDefinition);

function CreateConstCode( Symbol: pConstSymbol): pCodeTree;

function GetLexLevel( Symbol: pSymbol): Integer;

function IsSigned( Def: pDefinition): Boolean;

procedure Remove0( var Str: String; Len: LongInt);
procedure DecodeRealConst( var Buf; const Str: String);

function GetSICompare( CodeType: tCodeType): tAsmOp;
function GetUICompare( CodeType: tCodeType): tAsmOp;
function GetFloatCompare( CodeType: tCodeType): tAsmOp;

function GetSIFlag( CodeType: tCodeType): tResultFlags;
function GetUIFlag( CodeType: tCodeType): tResultFlags;
function GetFloatFlag( CodeType: tCodeType): tResultFlags;

function GetJUMP( ResFlag: tResultFlags): tAsmOp;
function GetJUMPr( ResFlag: tResultFlags): tAsmOp;
function GetSET( ResFlag: tResultFlags): tAsmOp;

function FlagNot( ResFlag: tResultFlags): tResultFlags;

implementation

uses StdLib, Config, Errors, PasComp, Compiler, FileColl;


function IsConst( Code: pCodeTree): Boolean;
  var
    S: String;
  begin
    if not Assigned( Code) then
      IsConst := True
    else
      begin
         case Code^.Node.CodeType of
           cctIntConst, cctOrdConst, cctRealConst,
           cctCharConst, cctStringConst, cctBoolConst, cctSetConst,
           cctPointerConst, cctFunction, cctTypeOfType, cctPCharConst:
             IsConst := True;
           cctLoadAddress:
             case Code^.Left^.Node.CodeType of
               cctFunction:
                 IsConst := True;
               cctVariable:
                 IsConst := Code^.Left^.Node.Symbol^.VarType = cvtGlobal;
               cctLoadValue:
                 begin
                 IsConst := (Code^.Left^.Left^.Node.CodeType = cctVariable) and
                   (Code^.Left^.Right^.Node.CodeType = cctIntConst);
                 end;
               else
                 IsConst := False;
             end;
           else
             IsConst := False;
        end;
      end;
  end;


function GetParamType( CodeTree: pCodeTree): tVariableType;
  begin
    if Assigned( CodeTree) then
      case CodeTree^.Node.CodeType of
        cctVariable:
          if CodeTree^.Node.Symbol^.VarType = cvtConstParam then
            GetParamType := cvtConstParam
          else
            GetParamType := cvtVarParam;
        cctAssignment,
        cctLoadValue:
          GetParamType := GetParamType( CodeTree^.Left);
        cctWithSymbol,
        cctDeref:
          GetParamType := cvtVarParam;
        cctTypeConversion:
          GetParamType := GetParamType( CodeTree^.Left);
        cctMem:
          GetParamType := cvtVarParam;
        else
          GetParamType := cvtParam
      end
    else
      GetParamType := cvtParam;
  end;


function GetOperatorType( Token: tToken): tPasOperators;
  var
    Op: tPasOperators;
  begin
    Op := cpoUnknown;
    case Token of
      ctPlus: Op := cpoPlus;
      ctMinus: Op := cpoMinus;
      ctStar: Op := cpoStar;
      ctSlash: Op := cpoSlash;
      ctDiv: Op := cpoDiv;
      ctMod: Op := cpoMod;
      ctEqual: Op := cpoEqual;
      ctUnequal: Op := cpoUnequal;
      ctGreater: Op := cpoGreater;
      ctLess: Op := cpoLess;
      ctGreaterEq: Op := cpoGreaterEqual;
      ctLessEq: Op := cpoLessEqual;
      ctAssignment: Op := cpoAssignment;
      ctAnd: Op := cpoAnd;
      ctIn: Op := cpoIn;
      ctOr: Op := cpoOr;
      ctShl: Op := cpoShl;
      ctShr: Op := cpoShr;
      ctXor: Op := cpoXor;
      ctPlusAsn: Op := cpoPlusAsn;
      ctMinusAsn: Op := cpoMinusAsn;
      ctAndAsn: Op := cpoAndAsn;
      ctOrAsn: Op := cpoOrAsn;
      ctStarAsn: Op := cpoStarAsn;
      ctSlashAsn: Op := cpoSlashAsn;
      ctDivAsn: Op := cpoDivAsn;
      ctModAsn: Op := cpoModAsn;
      ctShlAsn: Op := cpoShlAsn;
      ctShrAsn: Op := cpoShrAsn;
      ctXorAsn: Op := cpoXorAsn;
      ctNot: Op := cpoNot;
    end;
    GetOperatorType := Op;
  end;


procedure DisposeFunctionStack( FuncStack: pFunctionStack);
  var
    FStack: pFunctionStack;
  begin
    while Assigned( FuncStack) do
      begin
        FStack := FuncStack;
        FuncStack := FuncStack^.Next;
        Dispose( FStack);
      end;
  end;


function GetEAX( Size: tSize): tRegister;
  begin
    case Size of
      csByte: GetEAX := crAL;
      csWord: GetEAX := crAX;
      csDWord: GetEAX := crEAX;
    end;
  end;

function GetEBX( Size: tSize): tRegister;
  begin
    case Size of
      csByte: GetEBX := crBL;
      csWord: GetEBX := crBX;
      csDWord: GetEBX := crEBX;
    end;
  end;

function GetECX( Size: tSize): tRegister;
  begin
    case Size of
      csByte: GetECX := crCL;
      csWord: GetECX := crCX;
      csDWord: GetECX := crECX;
    end;
  end;

function GetEDX( Size: tSize): tRegister;
  begin
    case Size of
      csByte: GetEDX := crDL;
      csWord: GetEDX := crDX;
      csDWord: GetEDX := crEDX;
    end;
  end;

function GetReg( Reg: tRegister; Size: tSize): tRegister;
  begin
    case Reg of
      crEAX: GetReg := GetEAX( Size);
      crECX: GetReg := GetECX( Size);
      crEBX: GetReg := GetEBX( Size);
      crEDX: GetReg := GetEDX( Size);
    else
      GetReg := Reg;
    end;
  end;


function GetRegL( Reg: tRegister): tRegister;
  begin
    case Reg of
      crEAX:
        GetRegL := crAL;
      crEBX:
        GetRegL := crBL;
      crECX:
        GetRegL := crCL;
      crEDX:
        GetRegL := crDL;
      else
        GetRegL := Reg;
    end;
  end;

function GetRegH( Reg: tRegister): tRegister;
  begin
    case Reg of
      crEAX:
        GetRegH := crAH;
      crEBX:
        GetRegH := crBH;
      crECX:
        GetRegH := crCH;
      crEDX:
        GetRegH := crDH;
      else
        GetRegH := Reg;
    end;
  end;



function GetSize( Size: LongInt): tSize;
  begin
    {$IFDEF TP}{$R-}{$ENDIF}
    case Size of
      1: GetSize := csByte;
      2: GetSize := csWord;
      4: GetSize := csDWord;
      8: GetSize := csQWord;
      10: GetSize := csTByte;
      else
        GetSize := csDefault
    end
    {$IFDEF DEBUG} {$R+} {$ENDIF}
  end;


function CreatePointerValue( CodeTree: pCodeTree): pPointerValue;
  var
    Symbol: pSymbol;
  begin
    CreatePointerValue := nil;
    case CodeTree^.Node.CodeType of
      cctLoadAddress:
        begin
        with CodeTree^.Left^ do
          case Node.CodeType of
            cctVariable:
              CreatePointerValue := NewPointerValue( Node.Symbol, nil, 0);
            cctFunction:
              CreatePointerValue := NewPointerValue( Node.FuncSym, nil, 0);
            cctLoadValue: if Right^.Node.CodeType = cctIntConst then
              case Left^.Node.CodeType of
                cctVariable:
                  CreatePointerValue :=
                    NewPointerValue( Left^.Node.Symbol, nil, Right^.Node.IntValue);
              end;
          end;
        end;
      cctPointerConst:
        CreatePointerValue := NewPointerValue(
          CodeTree^.Node.PointerSymbol, nil, CodeTree^.Node.PointerValue);
      cctTypeOfType:
        CreatePointerValue := NewPointerValue(
          nil, NewStr( CodeTree^.Node.ObjectDef^.GetVMTName{$IFDEF PPRO}(){$ENDIF}), 0);
    end;
  end;


function ReverseDefColl( DefColl: pDefCollection): pDefCollection;
  var
    P, DC, Defs: pDefCollection;
  begin
    P := nil;
    Defs := DefColl;
    while Assigned( Defs) do
      begin
        New( DC);
        DC^.Definition := Defs^.Definition;
        DC^.ParamType := Defs^.ParamType;
        DC^.Next := P;
        P := DC;
        Defs := Defs^.Next;
      end;
    ReverseDefColl := P;
  end;


function _LEA_( Register: tRegister; Reference: tReference): pAsmInstruction;
  begin
    _LEA_ := New( pAsmInstruction, Create_Reg_Ref(
      caiLEA, Register, Reference));
  end;

function _PUSH_( Register: tRegister): pAsmInstruction;
  begin
    _PUSH_ := New( pAsmInstruction, Create_Reg(
      caiPUSH, Register));
  end;

function _PUSH_const( Value: LongInt): pAsmInstruction;
  begin
    _PUSH_const := New( pAsmInstruction, Create_Const(
      caiPUSH, Value));
  end;

function _POP_( Register: tRegister): pAsmInstruction;
  begin
    _POP_ := New( pAsmInstruction, Create_Reg(
      caiPOP, Register));
  end;


function LoadUnitFile( const aUnitName, aFileName: String): Integer;
  var
    FileName: String;
    Header: String;
    S: pUnitStream;
    UsedFiles: pFileDateCollection;
    UsedUnits: pFileCollection;
    UnitSymbols: pSymbolTable;
    I: tIndex;
    fdi: pFileDateItem;
    UName: pString;
    UI: pUnitItem;
    OldCompiler: pCompiler;
    Pos: LongInt;
  begin
    if Assigned( UnitCollection) and
      UnitCollection^.Search( @aUnitName, I) then
      begin
        UI := UnitCollection^.At( I);
        if not Assigned( UI^.SymbolTable) then
          begin
            Compile( aUnitName);
            LoadUnitFile := cluUnitRecompiled;
            Exit;
          end;
        if UI^.IsUnitCompiled then
          begin
            LoadUnitFile := cluUnitRecompiled;
            if not UI^.IsInterfaceReady and Assigned( UI^.Compiler) then
              begin
                pCompiler( UI^.Compiler)^.Reset;
                OldCompiler := CurCompiler;
                CurCompiler := UI^.Compiler;
                pCompiler( UI^.Compiler)^.CompileUnit;
                CurCompiler := OldCompiler;
                while Assigned( pCompiler( UI^.Compiler)^.Files) do
                  pCompiler( UI^.Compiler)^.DeleteFile;
              end;
          end
        else
          LoadUnitFile := cluNormal;
        Exit;
      end;
    if Assigned( UnitCollection) then
      UnitCollection^.Insert( CreateUnitItem( aUnitName, nil, nil, nil));
    if FindFile( aFileName + UnitExt, FileName, UnitSearchPath) then
      begin
        S := New( pUnitStream, Init( FileName, stOpenRead));
        {if S^.Status <> stOK then
          CurCompiler^.Error( erFileAccessDenied, CurCompiler^.Files^.PrevLine,
            CurCompiler^.Files^.PrevCol, FileName);}
        {S^.Read( Header[1], Length( UnitHeader));
        Header[0] := UnitHeader[0];
        if (Header <> UnitHeader) or (S^.Status <> stOK) then
          CurCompiler^.Error( erUnitFileFormatError,
            CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol, FileName);}

        {UsedFiles := pFileDateCollection( S^.Get);}
        UsedFiles := New( pFileDateCollection, Load( S^));
        Pos := S^.GetPos;
        Dispose( S, Done);
        for I := 0 to UsedFiles^.Count - 1 do
          begin
            fdi := UsedFiles^.At( I);
            if Assigned( fdi) and Assigned( fdi^.FileName) then
              if FExists( fdi^.FileName^) then
                if GetFileTime( fdi^.FileName^) <> fdi^.DateTime then
                  begin
                    Dispose( UsedFiles, Done);
                    {Dispose( S, Done);}
                    Compile( aUnitName);
                    LoadUnitFile := cluUnitRecompiled;
                    Exit;
                  end;
          end;
        Dispose( UsedFiles, Done);

        S := New( pUnitStream, Init( FileName, stOpenRead));
        S^.Seek( Pos);
        {UsedUnits := pFileCollection( S^.Get);}
        UsedUnits := New( pFileCollection, Load( S^));
        Pos := S^.GetPos;
        Dispose( S, Done);
        for I := 0 to UsedUnits^.Count - 1 do
          begin
            UName := UsedUnits^.At( I);
            if LoadUnitFile( UName^, UName^) and cluUnitRecompiled <> 0 then
              begin
                UI := nil;
                if UnitCollection^.Search( @aUnitName, I) then
                  UI := UnitCollection^.At( I);
                Dispose( UsedUnits, Done);
                {Dispose( S, Done);}
                if not Assigned( UI) or not UI^.IsUnitCompiled then
                  Compile( aUnitName);
                LoadUnitFile := cluUnitRecompiled;
                Exit;
              end;
          end;
        S := New( pUnitStream, Init( FileName, stOpenRead));
        S^.Seek( Pos);
        {Dispose( UsedUnits, Done);}
      end
    else
      begin
        Compile( aUnitName);
        LoadUnitFile := cluUnitRecompiled;
        Exit;
      end;
    {UnitSymbols := pSymbolTable( S^.Get);}
    UnitSymbols := New( pSymbolTable, Load( S^));
    UnitSymbols^.SymbolTableType := stUnitTable;
    UnitSymbols^.Name := NewStr( aUnitName);
    UnitCollection^.Search( @aUnitName, I);
    UI := UnitCollection^.At( I);
    UI^.SymbolTable := UnitSymbols;
    UI^.UsedUnits := UsedUnits;
    {UI^.LinkFiles := pFileCollection( S^.Get);}
    UI^.LinkFiles := New( pFileCollection, Load( S^));
    Dispose( S, Done);
    for I := 0 to UnitSymbols^.Count - 1 do
      ResolveDefinitions( UnitSymbols^.At(I), UnitSymbols);
    LoadUnitFile := cluNormal;
  end;


function EqualHeaders( Func1, Func2: pFunctionSymbol): Boolean;
  var
    ST1, ST2: pSymbolTable;
    S1, S2: pVariableSymbol;
    I: LongInt;
  begin
    EqualHeaders := False;
    if Assigned( Func1^.Definition) and Assigned( Func2^.Definition) then
      begin
        ST1 := Func1^.Definition^.LocalSymbols;
        ST2 := Func2^.Definition^.LocalSymbols;
        if Assigned( ST1) and Assigned( ST2) and
          (ST1^.Count = ST2^.Count) then
            begin
              for I := 0 to ST1^.Count - 1 do
                begin
                  S1 := ST1^.At( I) ;
                  S2 := ST2^.At( I);
                  if (S1^.SymbolName^ <> S2^.SymbolName^) or
                    (S1^._Type <> cVariableSymbol) or
                    (S2^._Type <> cVariableSymbol) or
                    (S1^.VarType <> S2^.VarType) or
                    not SameTypes( S1^.Definition, S2^.Definition) then
                      Exit;
                end;
              EqualHeaders := True;
            end;
      end;
  end;


function IsAncestor( ODef1, ODef2: pObjectDefinition): Boolean;
  begin
    IsAncestor := False;
    if Assigned( ODef1) and Assigned( ODef2) and
      (ODef1^.DefType = cObjectDefinition) and
      (ODef2^.DefType = cObjectDefinition) then
      begin
        ODef2 := ODef2^.Ancestor;
        while Assigned( ODef2) do
          begin
            if ODef2 = ODef1 then
              begin
                IsAncestor := True;
                Exit;
              end;
            ODef2 := ODef2^.Ancestor;
          end;
      end;
  end;


function GetUnitTable( Symbol: pSymbol): pSymbolTable;
  var
    SymbolTable: pSymbolTable;
  begin
    SymbolTable := nil;
    while Assigned( Symbol) and (Symbol^._Type <> cUnitSymbol) do
      begin
        SymbolTable := Symbol^.Owner;
        if not Assigned( SymbolTable) then
          Symbol := nil
        else
          begin
            case SymbolTable^.SymbolTableType of
              stGlobalTable,
              stUnitTable:
                break;
              stLocalTable:
                Symbol := pSymbol( SymbolTable^.Owner);
              stRecordTable,
              stObjectTable:
                Symbol := pDefinition( SymbolTable^.Owner)^.Symbol;
              else
                Symbol := nil;
            end;
          end;
      end;
    GetUnitTable := SymbolTable;
  end;


function GetBaseType( Min, Max: LongInt): tBaseType;
  var
    S, S1: Byte;
  begin
    if Min < 0 then
      begin
        if (Min >= -128) and (Max < 128) then
          GetBaseType := cbtShortInt
        else if (Min >= -32768) and (Max < 32768) then
          GetBaseType := cbtInteger
        else
          GetBaseType := cbtLongInt;
      end
    else
      begin
        if Max < 256 then
          GetBaseType := cbtByte
        else if Max < 65536 then
          GetBaseType := cbtWord
        else
          GetBaseType := cbtDWord;
      end;
  end;


procedure DisposePointerValue( Val: pPointerValue);
  begin
    if Assigned( Val) then
      begin
        if Assigned( Val^.AsmLabel) then
          DisposeStr( Val^.AsmLabel);
        Dispose( Val);
      end;
  end;

procedure DisposeRecordValue( Val: pValueArray; Fields: pSymbolTable; Count: LongInt);
  var
    I: LongInt;
  begin
    for I := 0 to Count - 1 do
      DisposeValue( Val^[ I], pVariableSymbol( Fields^.At( I))^.Definition);
    FreeMem( Val, Count * SizeOf( tValue));
  end;

procedure DisposeArrayValue( Val: pValueArray; IndexDef, ComDef: pDefinition; Count: LongInt);
  var
    L, C: LongInt;
  begin
    for L := 0 to Count - 1 do
      DisposeValue( Val^[ L], ComDef);
    FreeMem( Val, Count * SizeOf( tValue));
  end;

procedure DisposeValue( var Value: tValue; Def: pDefinition);
  begin
    case Value.ValueType of
      cvStringValue,
      cvPCharValue,
      cvASCIIZValue:
        DisposeStr( Value.StringValue);
      cvSetValue:
        FreeMem( Value.InfoPtr, 32);
      cvRecordValue:
        DisposeRecordValue( Value.InfoPtr, pRecordDefinition( Def)^.Fields,
          pRecordDefinition( Def)^.GetCount);
      cvArrayValue:
        DisposeArrayValue( Value.InfoPtr, pArrayDefinition( Def)^.IndexDef,
          pArrayDefinition( Def)^.ComponentDef,
          pArrayDefinition( Def)^.GetCount);
      cvAddressValue,
      cvProceduralValue:
        DisposePointerValue( Value.InfoPtr);
      cvCharArrayValue:
        FreeMem( Value.InfoPtr, pArrayDefinition( Def)^.GetCount);
    end;
  end;


function CreateConstCode( Symbol: pConstSymbol): pCodeTree;
  begin
    case Symbol^.Value.ValueType of
      cvOrdinalValue:
        CreateConstCode := New( pCodeTree, CreateOrdConst(
          Symbol^.Value.IntValue, Symbol^.ConstType,
            CurCompiler^.Files^.PrevLine,
            CurCompiler^.Files^.PrevCol));
      cvRealValue:
        CreateConstCode := New( pCodeTree,
          CreateRealConst( Symbol^.Value.RealValue,
            Symbol^.ConstType,
            CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol));
      cvStringValue:
        CreateConstCode := New( pCodeTree,
          CreateStringConst( Symbol^.Value.StringValue^,
          Symbol^.ConstType,
          CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol));
      cvSetValue:
        CreateConstCode := New( pCodeTree,
          CreateSetConst( tByteSet( Symbol^.Value.InfoPtr^),
            Symbol^.ConstType,
            CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol));
      cvAddressValue:
        CreateConstCode := New( pCodeTree, CreatePointerConst(
          pPointerValue( Symbol^.Value.InfoPtr)^.Offset,
          pPointerValue( Symbol^.Value.InfoPtr)^.Symbol,
          pPointerValue( Symbol^.Value.InfoPtr)^.AsmLabel,
          Symbol^.ConstType,
          CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol));
    end;
  end;


function GetLexLevel( Symbol: pSymbol): Integer;
  begin
    GetLexLevel := 0;
    if Assigned( Symbol) and Assigned( Symbol^.Owner) and
      Assigned( Symbol^.Owner^.Owner) and
      (TypeOf( Symbol^.Owner^.Owner^) = TypeOf( tFunctionDefinition)) then
      GetLexLevel := pFunctionDefinition( Symbol^.Owner^.Owner)^.LexLevel;
  end;


function IsSigned( Def: pDefinition): Boolean;
  begin
    IsSigned := Assigned( Def) and (Def^.DefType = cOrdDefinition) and
      (pOrdDefinition( Def)^.BaseType in [ cbtShortInt, cbtInteger, cbtLongInt]);
  end;


procedure Remove0( var Str: String; Len: LongInt);
  begin
    while Length( Str) > Len do
      if Str[ 1] = '0' then
        Delete( Str, 1, 1)
      else
        break;
  end;

function CharToByte( Ch: Char): Byte;
  begin
    case UpCase( Ch) of
      '0'..'9':
        CharToByte := Ord( Ch) - Ord( '0');
      'A'..'F':
        CharToByte := Ord( UpCase( Ch)) - (Ord( 'A') - 10);
    end;
  end;

procedure DecodeRealConst( var Buf; const Str: String);
  var
    I, J: LongInt;
    B: Byte;
  begin
    J := 0;
    for I := Length( Str) shr 1 downto 1 do
      begin
        B := CharToByte( Str[ I*2]) + CharToByte( Str[ I*2 - 1]) shl 4;
        tByteArray( Buf)[ J] := B;
        Inc( J);
      end;
  end;


function GetSICompare( CodeType: tCodeType): tAsmOp;
  begin
    case CodeType of
      cctEqual:
        GetSICompare := caiSETZ;
      cctUnequal:
        GetSICompare := caiSETNZ;
      cctGreater:
        GetSICompare := caiSETG;
      cctLess:
        GetSICompare := caiSETL;
      cctGreaterEq:
        GetSICompare := caiSETGE;
      cctLessEq:
        GetSICompare := caiSETLE;
    end;
  end;

function GetUICompare( CodeType: tCodeType): tAsmOp;
  begin
    case CodeType of
      cctEqual:
        GETUICompare := caiSETZ;
      cctUnequal:
        GetUICompare := caiSETNZ;
      cctGreater:
        GetUICompare := caiSETA;
      cctLess:
        GetUICompare := caiSETB;
      cctGreaterEq:
        GetUICompare := caiSETAE;
      cctLessEq:
        GetUICompare := caiSETBE;
    end;
  end;

function GetFloatCompare( CodeType: tCodeType): tAsmOp;
  begin
    case CodeType of
      cctEqual:
        GetFloatCompare := caiSETZ;
      cctUnequal:
        GetFloatCompare := caiSETNZ;
      cctGreater:
        GetFloatCompare := caiSETB;
      cctLess:
        GetFloatCompare := caiSETA;
      cctGreaterEq:
        GetFloatCompare := caiSETBE;
      cctLessEq:
        GetFloatCompare := caiSETAE;
    end;
  end;

function GetSIFlag( CodeType: tCodeType): tResultFlags;
  begin
    case CodeType of
      cctEqual:
        GetSIFlag := cfEqual;
      cctUnequal:
        GetSIFlag := cfNotEqual;
      cctGreater:
        GetSIFlag := cfGreater;
      cctLess:
        GetSIFlag := cfLess;
      cctGreaterEq:
        GetSIFlag := cfGreaterEqual;
      cctLessEq:
        GetSIFlag := cfLessEqual;
    end;
  end;

function GetUIFlag( CodeType: tCodeType): tResultFlags;
  begin
    case CodeType of
      cctEqual:
        GetUIFlag := cfEqual;
      cctUnequal:
        GetUIFlag := cfNotEqual;
      cctGreater:
        GetUIFlag := cfAbove;
      cctLess:
        GetUIFlag := cfBelow;
      cctGreaterEq:
        GetUIFlag := cfAboveEqual;
      cctLessEq:
        GetUIFlag := cfBelowEqual;
    end;
  end;

function GetFloatFlag( CodeType: tCodeType): tResultFlags;
  begin
    case CodeType of
      cctEqual:
        GetFloatFlag := cfEqual;
      cctUnequal:
        GetFloatFlag := cfNotEqual;
      cctGreater:
        GetFloatFlag := cfBelow;
      cctLess:
        GetFloatFlag := cfAbove;
      cctGreaterEq:
        GetFloatFlag := cfBelowEqual;
      cctLessEq:
        GetFloatFlag := cfAboveEqual;
    end;
  end;


function GetJUMP( ResFlag: tResultFlags): tAsmOp;
  begin
    case ResFlag of
      cfEqual:
        GetJUMP := caiJZ;
      cfNotEqual:
        GetJUMP := caiJNZ;
      cfGreater:
        GetJUMP := caiJG;
      cfGreaterEqual:
        GetJUMP := caiJGE;
      cfLess:
        GetJUMP := caiJL;
      cfLessEqual:
        GetJUMP := caiJLE;
      cfAbove:
        GetJUMP := caiJA;
      cfAboveEqual:
        GetJUMP := caiJAE;
      cfBelow:
        GetJUMP := caiJB;
      cfBelowEqual:
        GetJUMP := caiJBE;
      cfCarry:
        GetJUMP := caiJC;
      cfNoCarry:
        GetJUMP := caiJNC;
    end;
  end;


function GetJUMPr( ResFlag: tResultFlags): tAsmOp;
  begin
    case ResFlag of
      cfEqual:
        GetJUMPr := caiJNZ;
      cfNotEqual:
        GetJUMPr := caiJZ;
      cfGreater:
        GetJUMPr := caiJLE;
      cfGreaterEqual:
        GetJUMPr := caiJL;
      cfLess:
        GetJUMPr := caiJGE;
      cfLessEqual:
        GetJUMPr := caiJG;
      cfAbove:
        GetJUMPr := caiJBE;
      cfAboveEqual:
        GetJUMPr := caiJB;
      cfBelow:
        GetJUMPr := caiJAE;
      cfBelowEqual:
        GetJUMPr := caiJA;
      cfCarry:
        GetJUMPr := caiJNC;
      cfNoCarry:
        GetJUMPr := caiJC;
    end;
  end;

function GetSET( ResFlag: tResultFlags): tAsmOp;
  begin
    case ResFlag of
      cfEqual:
        GetSET := caiSETZ;
      cfNotEqual:
        GetSET := caiSETNZ;
      cfGreater:
        GetSET := caiSETG;
      cfGreaterEqual:
        GetSET := caiSETGE;
      cfLess:
        GetSET := caiSETL;
      cfLessEqual:
        GetSET := caiSETLE;
      cfAbove:
        GetSET := caiSETA;
      cfAboveEqual:
        GetSET := caiSETAE;
      cfBelow:
        GetSET   := caiSETB;
      cfBelowEqual:
        GetSET := caiSETBE;
      cfCarry:
        GetSET := caiSETC;
      cfNoCarry:
        GetSET := caiSETNC;
    end;
  end;


function FlagNot( ResFlag: tResultFlags): tResultFlags;
  begin
    case ResFlag of
      cfEqual:
        FlagNot := cfNotEqual;
      cfNotEqual:
        FlagNot := cfEqual;
      cfGreater:
        FlagNot := cfLessEqual;
      cfGreaterEqual:
        FlagNot := cfLess;
      cfLess:
        FlagNot := cfGreaterEqual;
      cfLessEqual:
        FlagNot := cfGreater;
      cfAbove:
        FlagNot := cfBelowEqual;
      cfAboveEqual:
        FlagNot := cfBelow;
      cfBelow:
        FlagNot := cfAboveEqual;
      cfBelowEqual:
        FlagNot := cfAbove;
      cfCarry:
        FlagNot := cfNoCarry;
      cfNoCarry:
        FlagNot := cfCarry;
    end;
  end;

end.