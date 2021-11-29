{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       Symbols unit                                                    }
{                                              (c) Copyright 1997-1998  }
{                                   Iggor Khachko - hachko@icl.kazan.su }
{-----------------------------------------------------------------------}

{
  Дата создания: 17.09.97
  Модуль SYMBOLS содержит кучу объектов, которые описывают свойства
  символов, типов данных.
}

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

unit Symbols;

interface

uses Dos, Objects, UnitStrm, Config, IAsm386, FileColl;

const

  stGlobalTable         = 1;
  stWithTable           = 2;
  stRecordTable         = 3;
  stObjectTable         = 4;
  stUnitTable           = 5;
  stStaticTable         = 6;
  stLocalTable          = 7;
  stParamTable          = 8;
  stMacrosTable         = 9;

  poNormal              = $0000;
  poAssembler           = $0001;
  poConstructor         = $0002;
  poDestructor          = $0004;
  poMethod              = $0008;
  poVirtualMethod       = $0010;
  poDinamicMethod       = $0020;
  poExternal            = $0040;

  ftAssembler           = 1;
  ftInterrupt           = 2;
  ftExternal            = 4;
  ftInline              = 8;

  csoPublicSymbol       = 1;
  csoPrivateSymbol      = 2;
  csoProtectedSymbol    = 3;

  cvOrdinalValue        = 0;
  cvRealValue           = 1;
  cvStringValue         = 2;
  cvRecordValue         = 3;
  cvArrayValue          = 4;
  cvAddressValue        = 5;
  cvProceduralValue     = 6;
  cvSetValue            = 7;
  cvCharArrayValue      = 8;
  cvASCIIZValue         = 9;
  cvPCharValue          = 10;


type

  pByteSet = ^tByteSet;
  tByteSet = Set of Byte;

  tByteArray = array [0..65534] of Byte;
  pNameString = ^tNameString;
  tNameString = String[127];

  pSymbol = ^tSymbol;

  pDefinition = ^tDefinition;
  pAbstractFunctionDefinition = ^tAbstractFunctionDefinition;
  pFunctionTypeDefinition = ^tFunctionTypeDefinition;
  pFunctionDefinition = ^tFunctionDefinition;
  pMainFunctionDefinition = ^tMainFunctionDefinition;
  pOrdDefininition = ^tOrdDefinition;
  pUserOrdDefinition = ^tUserOrdDefinition;
  pBooleanDefinition = ^tBooleanDefinition;
  pRealDefinition = ^tRealDefinition;
  pStringDefinition = ^tStringDefinition;
  pArrayDefinition = ^tArrayDefinition;
  pRecordDefinition = ^tRecordDefinition;
  pPointerDefinition = ^tPointerDefinition;
  pFileDefinition = ^tFileDefinition;
  pSetDefinition = ^tSetDefinition;
  pObjectDefinition = ^tObjectDefinition;

  tSymbolType = (cAbstractSymbol, cProgramSymbol, cUnitSymbol,
    cFunctionSymbol, cOperatorSymbol, cTypeSymbol, cConstSymbol,
    cTypedConstSymbol, cLabelSymbol, cVariableSymbol, cMacroSymbol,
    cUserOrdSymbol, cSystemSymbol, cAbsoluteSymbol);

  tBaseType = (cbtByte, cbtShortInt, cbtChar, cbtWord,
    cbtInteger, cbtDWord, cbtLongInt);

  tRealType = ( crtSingle, crtDouble, crtExtended, crtComp);

  tBoolType = ( cbBoolean, cbWordBool, cbLongBool);

  tSetType = ( cstSmallSet, cstNormalSet);

  tPasOperators = ( cpoUnknown,
    cpoPlus, cpoMinus, cpoStar, cpoSlash, cpoDiv, cpoMod, cpoEqual,
    cpoUnequal, cpoGreater, cpoLess, cpoGreaterEqual, cpoLessEqual, cpoAssignment,
    cpoAnd, cpoIn, cpoOr, cpoShl, cpoShr, cpoXor, cpoPlusAsn, cpoMinusAsn,
    cpoAndAsn, cpoOrAsn, cpoStarAsn, cpoSlashAsn, cpoDivAsn, cpoModAsn,
    cpoShlAsn, cpoShrAsn, cpoXorAsn, cpoNot
  );

  tSystemSymbolType = ( csstWrite, csstWriteLn, csstRead, csstReadLn,
    csstAssign, csstAbs, csstOdd, csstSizeOf, csstOfs, csstTypeOf, csstPred,
    csstSucc, csstStr, csstInc, csstDec, csstChr, csstOrd, csstLength,
    csstAddr, csstAssigned, csstHigh, csstLow, csstConcat,
    csstInclude, csstExclude, csstMem, csstMemW, csstMemL, csstPort,
    csstPortW, csstPortL,

    csstSin, csstCos, csstTan, csstArcTan, csstSqr, csstSqrt, csstCotan,
    csstPI
  );

{$IFDEF TP}
  tIndex = Integer;
{$ENDIF}

  pSymbolTable = ^tSymbolTable;
  tSymbolTable = object(tCollection)
    Next: pSymbolTable;
    SymbolTableType: Word;
    Name: pString;
    Owner: pObject;
    DataSize: LongInt;
    IsCompileInterface: Boolean;
    HasInitOffset: LongInt;
    HasInit: Boolean;
    Root: pSymbol;

    constructor Init(STType: Word; aLimit, aDelta: Integer);
    constructor Load(var S: TStream);
    destructor Done; virtual;
    procedure Store(var S: TStream);
    function Compare(Key1, Key2: Pointer): LongInt; virtual;
    function KeyOf(Item: Pointer): Pointer; virtual;
    procedure Insert(Item: Pointer); virtual;
    function Search( const SymbolName: String): Pointer;
    function GetName: String; virtual;
    function FindSymbol( const aName: tNameString): pSymbol;
    function FindWithAlias( const aName: tNameString): pSymbol;
    function GetItem(var S: TStream): Pointer; virtual;
    procedure PutItem(var S: TStream; Item: Pointer); virtual;
    procedure InsertToTree( Item: Pointer);
  end;

  tSymbol = object(tObject)
    _Type: tSymbolType;
    SymbolName: pString;
    Owner: pSymbolTable;
    isForward: Boolean;
    Options: LongInt;
    Left: pSymbol;
    Right: pSymbol;
    FastValue: LongInt;
    Weight: LongInt;

    constructor Init( const aName: tNameString; anOptions: LongInt);
    constructor Load(var S: TStream);
    destructor Done; virtual;
    procedure Store(var S: TStream); virtual;
    function Name: tNameString; virtual;
    function AsmName: String; virtual;
    procedure SetName( const NewName: tNameString);
    procedure WriteTo( S: pStream); virtual;
  end;

  pProgramSymbol = ^tProgramSymbol;
  tProgramSymbol = object(tSymbol)
    SymbolTable: pSymbolTable;
    constructor Init( const aName: tNameString; aSymbolTable: pSymbolTable);
  end;

  pUnitSymbol = ^tUnitSymbol;
  tUnitSymbol = object(tSymbol)
    UnitSymbols: pSymbolTable;
    UsedUnits: pFileCollection;
    UsedFiles: pFileDateCollection;
    LinkFiles: pFileCollection;

    constructor Init( const aName: tNameString; aUnitSymbols: pSymbolTable;
      aLinkFiles: pFileCollection);
    constructor Load(var S: TStream);
    constructor LoadUnit( const aSymbolName: tNameString; const FileName: PathStr);
    destructor Done; virtual;
    procedure Store(var S: TStream); virtual;
    procedure WriteUnit( const FileName: PathStr);
    {procedure ReadUnitFile( const FileName: PathStr);}
  end;

  pFunctionSymbol = ^tFunctionSymbol;
  tFunctionSymbol = object(tSymbol)
    Definition: pFunctionDefinition;
    Alias: pString;
    IsMain: Boolean;
    NextOverloaded: pFunctionSymbol;
    _AsmName: pString;
    constructor Init( const aName: tNameString; _IsMain: Boolean; anOptions: LongInt);
    destructor Done; virtual;
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    procedure WriteTo( S: pStream); virtual;
    function AsmName: String; virtual;
  end;

  pOperatorSymbol = ^tOperatorSymbol;
  tOperatorSymbol = object(tFunctionSymbol)
    _Operator: tPasOperators;
    constructor Init( aOperator: tPasOperators; anOptions: LongInt);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
  end;

  pTypeSymbol = ^tTypeSymbol;
  tTypeSymbol = object(tSymbol)
    Definition: pDefinition;
    IsOwner: Boolean;
    constructor Init(const aName: tNameString; aDefinition: pDefinition; anOptions: LongInt);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    destructor Done; virtual;
  end;

  pPointerValue = ^tPointerValue;
  tPointerValue = record
    Symbol: pSymbol;
    AsmLabel: pString;
    Offset: LongInt;
  end;

  tValue = record
    case ValueType: Integer of
      0: (CharValue: Char);
      1: (IntValue: LongInt);
      2: (RealValue: Extended);
      3: (StringValue: pString);
      4: (BoolValue: Boolean);
      5: (InfoPtr: Pointer);
  end;

  pValueArray = ^tValueArray;
  tValueArray = array [0..65520 div SizeOf( tValue)] of tValue;

  pConstSymbol = ^tConstSymbol;
  tConstSymbol = object(tSymbol)
    ConstType: pDefinition;
    Value: tValue;
    constructor Init(const aName: tNameString; ValType: Integer; var aValue; aType: pDefinition; anOptions: LongInt);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    destructor Done; virtual;
  end;

  pLabelSymbol = ^tLabelSymbol;
  tLabelSymbol = object(tSymbol)
    IsAssigned: Boolean;
    IsDefined: Boolean;
    constructor Init(const aName: tNameString; anOptions: LongInt);
    function AsmName: String; virtual;
  end;

  tVariableType = ( cvtUnknown, cvtGlobal, cvtLocal, cvtParam, cvtVarParam,
    cvtConstParam, cvtStringParam, cvtField);

  pVariableSymbol = ^tVariableSymbol;
  tVariableSymbol = object(tSymbol)
    Definition: pDefinition;
    Offset: LongInt;
    VarType: tVariableType;
    IsRegisterable: Boolean;
    Register: tRegister;
    IsOwner: Boolean;
    constructor Init(const aName: tNameString; aTypeDef: pDefinition;
      aVarType: tVariableType; anOptions: LongInt);
    destructor Done; virtual;
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function AsmName: String; virtual;
    function Size: LongInt;
    function IsGlobal: Boolean;
    procedure WriteTo( S: pStream); virtual;
  end;

  pTypedConstSymbol = ^tTypedConstSymbol;
  tTypedConstSymbol = object(tVariableSymbol)
    Value: tValue;
    constructor Init(const aName: tNameString; aTypeDef: pDefinition;
      anOptions: LongInt);
    destructor Done; virtual;
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    procedure WriteTo( S: pStream); virtual;
    procedure WriteValue( S: pStream);
    procedure DisposeValue;
    function AsmName: String; virtual;
  end;

  tAbsoluteType = ( catAddress, catVariable);

  pAbsoluteSymbol = ^tAbsoluteSymbol;
  tAbsoluteSymbol = object( tVariableSymbol)
    AbsoluteType: tAbsoluteType;
    Reference: pVariableSymbol;
    constructor Init(const aName: tNameString; aTypeDef: pDefinition;
      aVarType: tVariableType; anOptions: LongInt;
      AbsType: tAbsoluteType; Ref: pVariableSymbol);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
  end;

  pMacroSymbol = ^tMacroSymbol;
  tMacroSymbol = object(tSymbol)
    constructor Init(const aName: tNameString);
  end;

  pUserOrdSymbol = ^tUserOrdSymbol;
  tUserOrdSymbol = object( tSymbol)
    Definition: pUserOrdDefinition;
    Value: LongInt;
    constructor Init( const aName: tNameString; aValue: LongInt; Def: pUserOrdDefinition;
      anOptions: LongInt);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
  end;

  pSystemSymbol = ^tSystemSymbol;
  tSystemSymbol = object( tSymbol)
    SystemType: tSystemSymbolType;
    constructor Init( const aName: tNameString; SysType: tSystemSymbolType;
      anOptions: LongInt);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
  end;


  tDefinitionType = (cAbstractDefinition, cArrayDefinition, cOrdDefinition,
    cRecordDefinition, cPointerDefinition, cStringDefinition,
    cObjectDefinition, cFileDefinition, cSetDefinition,
    cRealDefinition, cFunctionTypeDefinition, cFunctionDefinition,
    cBooleanDefinition, cUserOrdDefinition);

  tDefinition = object(tObject)
    Symbol: pSymbol;
    DefType: tDefinitionType;
    Line, Col: LongInt;

    NextDefinition: pDefinition;

    constructor Init;
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function GetSize: LongInt; virtual;
    function GetName: String; virtual;
  end;

  pDefCollection = ^tDefCollection;
  tDefCollection = record
    Definition: pDefinition;
    ParamType: tVariableType;
    Next: pDefCollection;
  end;

  tCallType = ( cctDefault, cctPascal, cctCDecl, cctStdCall, cctRegister);

  tAbstractFunctionDefinition = object(tDefinition)
    {Parameters: pSymbolTable;}
    ParamColl: pDefCollection;
    ParamSize: LongInt;
    Options: Word;
    ResType: pDefinition;
    CallType: tCallType;
    constructor Init( Result: pDefinition);
    destructor Done; virtual;
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    {procedure InitParameters; virtual;}
  end;

  tFunctionTypeDefinition = object( tAbstractFunctionDefinition)
    constructor Init( Result: pDefinition);
    function GetSize: LongInt; virtual;
  end;

  tFunctionDefinition = object(tAbstractFunctionDefinition)
    LocalSymbols: pSymbolTable;
    Code: Pointer;
    LexLevel: Byte;
    LocalSize: LongInt;
    ProcOptions: LongInt;
    ObjectDef: pObjectDefinition;
    VirtualIndex: LongInt;
    constructor Init( Result: pDefinition; aLevel: Byte; anObjectDef: pObjectDefinition);
    constructor Load( var S: tStream);
    procedure Store( var S: tStream); virtual;
    destructor Done; virtual;
    procedure InitLocalSymbols; virtual;
    procedure WriteTo( S: pStream);
    procedure GenEntryExit( AsmProc: Pointer); virtual;
    function GetPostfix: String;
    procedure DisposeLocalSymbols;
    procedure SetCallType( NewCallType: tCallType);
  end;

  tMainFunctionDefinition = object( tFunctionDefinition)
    constructor Init;
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    procedure InitLocalSymbols; virtual;
    procedure GenEntryExit( AsmProc: Pointer); virtual;
  end;

  pOrdDefinition = ^tOrdDefinition;
  tOrdDefinition = object( tDefinition)
    BaseType: tBaseType;
    Min: LongInt;
    Max: LongInt;
    constructor Init( aBaseType: tBaseType; aMin, aMax: LongInt);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function GetSize: LongInt; virtual;
  end;

  tRealDefinition = object( tDefinition)
    RealType: tRealType;
    constructor Init( aType: tRealType);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function GetSize: LongInt; virtual;
  end;

  tStringDefinition = object( tDefinition)
    Length: Byte;
    constructor Init( aLength: Byte);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function GetSize: LongInt; virtual;
    function GetName: String; virtual;
  end;

  tPointerDefinition = object( tDefinition)
    DefinitionType: pDefinition;
    DefSym: pSymbol;
    constructor Init( aDef: pDefinition);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function GetSize: LongInt; virtual;
  end;

  tBooleanDefinition = object( tDefinition)
    BoolType: tBoolType;
    constructor Init( aType: tBoolType);
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function GetSize: LongInt; virtual;
  end;

  tUserOrdDefinition = object( tDefinition)
    Max: LongInt;
    constructor Init;
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function GetSize: LongInt; virtual;
  end;

  tRecordDefinition = object(tDefinition)
    Fields: pSymbolTable;
    constructor Init( aFields: pSymbolTable);
    destructor Done; virtual;
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function GetSize: LongInt; virtual;
    function GetCount: LongInt;
  end;

  tArrayDefinition = object( tDefinition)
    ComponentDef: pDefinition;
    IndexDef: pDefinition;
    ReadComponent, ReadIndex: Boolean;
    constructor Init( aComponent, aIndex: pDefinition);
    destructor Done; virtual;
    constructor Load(var S: TStream);
    procedure Store(var S: TStream); virtual;
    function GetSize: LongInt; virtual;
    function GetCount: LongInt;
  end;

  tFileType = ( cftTextFile, cftUntyped, cftTyped );

  tFileDefinition = object( tDefinition)
    FileType: tFileType;
    FileDef: pDefinition;
    ReadFileDef: Boolean;
    constructor Init( aFileType: tFileType; aFileDef: pDefinition);
    constructor Load( var S: tStream);
    procedure Store( var S: tStream); virtual;
    function GetSize: LongInt; virtual;
  end;

  tSetDefinition = object( tDefinition)
    SetDef: pDefinition;
    SetType: tSetType;
    Min, Max: LongInt;
    ReadDef: Boolean;
    constructor Init( aSetDef: pDefinition);
    constructor Load( var S: tStream);
    destructor Done; virtual;
    procedure Store( var S: tStream); virtual;
    function GetSize: LongInt; virtual;
  end;

  {pVMTitem = ^tVMTitem;
  tVMTitem = record
    Symbol: pFunctionSymbol;
    Next: pVmtItem;
  end;

  pVmtRec = ^tVmtRec;
  tVmtRec = record
    DMTTable: Pointer;
    VMethods: pVMTitem;
  end;}

  pVMT = ^tVMT;
  tVMT = object( tCollection)
    constructor Load( var S: tStream);
    procedure Store( var S: tStream);
    procedure FreeItem( Item: Pointer); virtual;
    function GetItem(var S: TStream): Pointer; virtual;
    procedure PutItem(var S: TStream; Item: Pointer); virtual;
  end;

  tObjectDefinition = object( tDefinition)
    Ancestor: pObjectDefinition;
    PublicSymbols: pSymbolTable;
    PrivateSymbols: pSymbolTable;
    VMTable: pVMT;
    constructor Init( aBase: pObjectDefinition);
    constructor Load( var S: tStream);
    destructor Done; virtual;
    procedure Store( var S: tStream); virtual;
    function GetSize: LongInt; virtual;
    function MustBeVirtual( Func: pFunctionSymbol): Boolean;
    function MakeVirtual( Func: pFunctionSymbol): Boolean;
    function GetVMTname: String;
    procedure WriteVMT( S: pStream);
  end;

  { Collection of units }
  pUnitItem = ^tUnitItem;
  tUnitItem = record
    UnitName: pString;
    SymbolTable: pSymbolTable;
    IsUnitCompiled: Boolean;
    IsInterfaceReady: Boolean;
    Compiler: Pointer;
    UsedUnits: pFileCollection;
    LinkFiles: pFileCollection;
  end;

  pUnitCollection = ^tUnitCollection;
  tUnitCollection = object( tSortedCollection)
    destructor Done; virtual;
    function Compare(Key1, Key2: Pointer): {$IFDEF PPRO}LongInt{$ELSE}Integer{$ENDIF}; virtual;
    function KeyOf(Item: Pointer): Pointer; virtual;
    procedure Insert( Item: Pointer); virtual;
    procedure FreeItem(Item: Pointer); virtual;
    function Search(Key: Pointer; var Index: tIndex): Boolean; virtual;
  end;

  pLongIntArray = ^tLongIntArray;
  tLongIntArray = array [0..16320] of LongInt;

  pSymbolPath = ^tSymbolPath;
  tSymbolPath = record
    UnitName: pString;
    PathLength: LongInt;
    Path: pLongIntArray;
  end;


procedure RegisterSymbols;
function IsNumeric( Def: pDefinition): Boolean;
procedure DisposeDefCollection( DefColl: pDefCollection);

procedure WriteDefinition( var S: TStream; Def: pDefinition; DoWrite: Boolean);
function ReadDefinition( var S: TStream; DoRead: Boolean): pDefinition;

procedure ResolveDefinitions( Symbol: pSymbol; SymTable: pSymbolTable);

procedure InitUnitCollection;
procedure DoneUnitCollection;
function CreateUnitItem( const UnitName: String; SymbolTable: pSymbolTable;
    UsedUnits: pFileCollection; LinkFiles: pFileCollection): pUnitItem;

procedure ReadConstValue( var S: tStream; var Value: tValue);
procedure WriteConstValue( var S: tStream; Value: tValue; ConstType: pDefinition);

function ReadSymbol( var S: tStream): pSymbol;

procedure Write_Symbol( var S: tStream; Symbol: pSymbol);
function Read_Symbol( var S: tStream): pSymbolPath;

function IsOldUnit( const FileName: PathStr): Boolean;

function SameTypes( Def1, Def2: pDefinition): Boolean;
function EqualTypes( Def1, Def2: pDefinition): Boolean;
function CompatibleTypes( Def1, Def2: pDefinition): Boolean;
function IsCompatible( Def1, Def2: pDefCollection): Boolean;
function IsSameParams( Def1, Def2: pDefCollection): Boolean;
function IsEqualParams( Def1, Def2: pDefCollection): Boolean;

function NewPointerValue( Symbol: pSymbol; AsmLabel: pString; Offset: LongInt): pPointerValue;

procedure DisposeDefinitions;

const

  UnitCollection: pUnitCollection = nil;

  RSymbol: TStreamRec = (
    ObjType: 1000;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tSymbol);
{$ENDIF}
    Load: @tSymbol.Load;
    Store: @tSymbol.Store
  );

  RSymbolTable: TStreamRec = (
    ObjType: 1001;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tSymbolTable)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tSymbolTable);
{$ENDIF}
    Load: @tSymbolTable.Load;
    Store: @tSymbolTable.Store
  );

  RUnitSymbol: TStreamRec = (
    ObjType: 1002;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tUnitSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tUnitSymbol);
{$ENDIF}
    Load: @tUnitSymbol.Load;
    Store: @tUnitSymbol.Store
  );

  RFunctionSymbol: TStreamRec = (
    ObjType: 1003;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tFunctionSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tFunctionSymbol);
{$ENDIF}
    Load: @tFunctionSymbol.Load;
    Store: @tFunctionSymbol.Store
  );

  ROperatorSymbol: TStreamRec = (
    ObjType: 1004;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tOperatorSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tOperatorSymbol);
{$ENDIF}
    Load: @tOperatorSymbol.Load;
    Store: @tOperatorSymbol.Store
  );

  RTypeSymbol: TStreamRec = (
    ObjType: 1005;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tTypeSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tTypeSymbol);
{$ENDIF}
    Load: @tTypeSymbol.Load;
    Store: @tTypeSymbol.Store
  );

  RConstSymbol: TStreamRec = (
    ObjType: 1006;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tConstSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tConstSymbol);
{$ENDIF}
    Load: @tConstSymbol.Load;
    Store: @tConstSymbol.Store
  );

  RVariableSymbol: TStreamRec = (
    ObjType: 1007;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tVariableSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tVariableSymbol);
{$ENDIF}
    Load: @tVariableSymbol.Load;
    Store: @tVariableSymbol.Store
  );

  RTypedConstSymbol: TStreamRec = (
    ObjType: 1008;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tTypedConstSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tTypedConstSymbol);
{$ENDIF}
    Load: @tTypedConstSymbol.Load;
    Store: @tTypedConstSymbol.Store
  );

  RUserOrdSymbol: TStreamRec = (
    ObjType: 1009;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tUserOrdSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tUserOrdSymbol);
{$ENDIF}
    Load: @tUserOrdSymbol.Load;
    Store: @tUserOrdSymbol.Store
  );

  RDefinition: TStreamRec = (
    ObjType: 1010;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tDefinition);
{$ENDIF}
    Load: @tDefinition.Load;
    Store: @tDefinition.Store
  );

  RFunctionDefinition: TStreamRec = (
    ObjType: 1011;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tFunctionDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tFunctionDefinition);
{$ENDIF}
    Load: @tFunctionDefinition.Load;
    Store: @tFunctionDefinition.Store
  );

  RMainFunctionDefinition: TStreamRec = (
    ObjType: 1012;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tMainFunctionDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tMainFunctionDefinition);
{$ENDIF}
    Load: @tMainFunctionDefinition.Load;
    Store: @tMainFunctionDefinition.Store
  );

  ROrdDefinition: TStreamRec = (
    ObjType: 1013;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tOrdDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tOrdDefinition);
{$ENDIF}
    Load: @tOrdDefinition.Load;
    Store: @tOrdDefinition.Store
  );

  RRealDefinition: TStreamRec = (
    ObjType: 1014;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tRealDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tRealDefinition);
{$ENDIF}
    Load: @tRealDefinition.Load;
    Store: @tRealDefinition.Store
  );

  RStringDefinition: TStreamRec = (
    ObjType: 1015;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tStringDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tStringDefinition);
{$ENDIF}
    Load: @tStringDefinition.Load;
    Store: @tStringDefinition.Store
  );

  RPointerDefinition: TStreamRec = (
    ObjType: 1016;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tPointerDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tPointerDefinition);
{$ENDIF}
    Load: @tPointerDefinition.Load;
    Store: @tPointerDefinition.Store
  );

  RArrayDefinition: TStreamRec = (
    ObjType: 1017;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tArrayDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tArrayDefinition);
{$ENDIF}
    Load: @tArrayDefinition.Load;
    Store: @tArrayDefinition.Store
  );

  RRecordDefinition: TStreamRec = (
    ObjType: 1018;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tRecordDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tRecordDefinition);
{$ENDIF}
    Load: @tRecordDefinition.Load;
    Store: @tRecordDefinition.Store
  );

  RBooleanDefinition: TStreamRec = (
    ObjType: 1019;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tBooleanDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tBooleanDefinition);
{$ENDIF}
    Load: @tBooleanDefinition.Load;
    Store: @tBooleanDefinition.Store
  );

  RUserOrdDefinition: TStreamRec = (
    ObjType: 1020;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tUserOrdDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tUserOrdDefinition);
{$ENDIF}
    Load: @tUserOrdDefinition.Load;
    Store: @tUserOrdDefinition.Store
  );

  RFileDefinition: TStreamRec = (
    ObjType: 1021;
{$IFDEF TP}
    VmtLink: Ofs( TypeOf( tFileDefinition)^ );
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf( tFileDefinition);
{$ENDIF}
    Load: @tFileDefinition.Load;
    Store: @tFileDefinition.Store
  );

  RSetDefinition: TStreamRec = (
    ObjType: 1022;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tSetDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tSetDefinition);
{$ENDIF}
    Load: @tSetDefinition.Load;
    Store: @tSetDefinition.Store
  );

  RFunctionTypeDefinition: TStreamRec = (
    ObjType: 1023;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tFunctionTypeDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tFunctionTypeDefinition);
{$ENDIF}
    Load: @tFunctionTypeDefinition.Load;
    Store: @tFunctionTypeDefinition.Store
  );

  RObjectDefinition: TStreamRec = (
    ObjType: 1024;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tObjectDefinition)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tObjectDefinition);
{$ENDIF}
    Load: @tObjectDefinition.Load;
    Store: @tObjectDefinition.Store
  );

  RVMT: TStreamRec = (
    ObjType: 1025;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tVMT)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tVMT);
{$ENDIF}
    Load: @tVMT.Load;
    Store: @tVMT.Store
  );

  RAbsoluteSymbol: TStreamRec = (
    ObjType: 1026;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tAbsoluteSymbol)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tAbsoluteSymbol);
{$ENDIF}
    Load: @tAbsoluteSymbol.Load;
    Store: @tAbsoluteSymbol.Store
  );


  FuncResultName: String[6] = 'RESULT';
  SelfName: String[4] = 'SELF';
  NameTerminate: String[9] = 'terminate';
  NameVMTTable: String[8] = 'vmttable';

  NameWriteLine: String[9] = 'writeline';
  NameReadLine: String[8] = 'readline';
  NameWriteString: String[11] = 'writestring';
  NameReadString: String[10] = 'readstring';
  NameWriteChar: String[9] = 'writechar';
  NameReadChar: String[8] = 'readchar';
  NameWriteSInt: String[9] = 'writesint';
  NameWriteUInt: String[9] = 'writeuint';
  NameReadInt: String[7] = 'readint';
  NameWriteReal: String[9] = 'writereal';
  NameReadReal: String[8] = 'readreal';
  NameWriteBoolean: String[12] = 'writeboolean';
  NameReadBoolean: String[11] = 'readboolean';

  NameWriteRecord: String[11] = 'writerecord';
  NameReadRecord: String[10] = 'readrecord';

  FuncNameSIntToString: String[12] = 'sinttostring';
  FuncNameUIntToString: String[12] = 'uinttostring';
  FuncNameRealToString: String[12] = 'realtostring';

  NameStrCat: String[6] = 'strcat';
  NameStrCopy: String[7] = 'strcopy';
  NameStrCompare: String[10] = 'strcompare';

  NameSetUnion: String[8] = 'setunion';
  NameSetDifference: String[13] = 'setdifference';
  NameSetIntersect: String[12] = 'setintersect';
  NameSetEqual: String[8] = 'setequal';
  NameSetSetItem: String[10] = 'setsetitem';
  NameSetSetRange: String[11] = 'setsetrange';
  NameSetLoad: String[7] = 'setload';
  NameSetStore: String[8] = 'setstore';
  NameSetIn: String[5] = 'setin';
  NameSetCompare: String[10] = 'setcompare';
  NameSetInclude: String[10] = 'setinclude';
  NameSetExclude: String[10] = 'setexclude';

  NameAssignText: String[10] = 'assigntext';
  NameAssignTyped: String[11] = 'assigntyped';
  NameAssignUntyped: String[13] = 'assignuntyped';

  NameNew: String[ 3] = 'new';
  NameDispose: String[ 7] = 'dispose';

  NameDispatchVirtual: String[15] = 'dispatchvirtual';
  NameDispatchDynamic: String[15] = 'dispatchdynamic';

  NameCopyObject: String[10] = 'copyobject';

  VMTstr: String[11] = '_$VMT$_';
  DMTstr: String[11] = '_$DMT$_';

  DefaultMacro: pSymbolTable = nil;

  OperatorNames: array [tPasOperators] of String [12] = (
    '',
    'plus',
    'minus',
    'star',
    'slash',
    'div',
    'mod',
    'equal',
    'unequal',
    'greater',
    'less',
    'greaterequal',
    'lessequal',
    'assignment',
    'and',
    'in',
    'or',
    'shl',
    'shr',
    'xor',
    'plusasn',
    'minusasn',
    'andasn',
    'orasn',
    'starasn',
    'slashasn',
    'divasn',
    'modasn',
    'shlasn',
    'shrasn',
    'xorasn',
    'not'
  );

implementation

uses StdLib, Tools, AsmOpt, AsmCode, CG_Flat, Code, Errors, Compiler;

const
  DefinitionList: pDefinition = nil;

constructor tSymbolTable.Init(STType: Word; aLimit, aDelta: Integer);
  begin
    inherited Init(aLimit, aDelta);
    {Duplicates := False;}
    SymbolTableType := STType;
    DataSize := 0;
    Owner := nil;
    IsCompileInterface := False;
    HasInit := False;
  end;

constructor tSymbolTable.Load(var S: TStream);

  procedure InsertNode( Item: Pointer); {$IFDEF TP} far;{$ENDIF}
    begin
      InsertToTree( Item);
    end;

  var
    L: LongInt;
    aLimit, aDelta, aCount: LongInt;
  begin
    S.Read( aLimit, SizeOf( LongInt));
    S.Read( aDelta, SizeOf( LongInt));
    S.Read( aCount, SizeOf( LongInt));
    inherited Init( aLimit, aDelta);
    Name := nil;
    Owner := nil;
    Next := nil;
    Root := nil;
    IsCompileInterface := False;
    {S.Read(SymbolTableType, SizeOf(SymbolTableType));}
    S.Read( DataSize, SizeOf( DataSize));
    L := S.GetPos;
    S.Read( HasInit, SizeOf( HasInit));
    for L := 0 to aCount - 1 do
      AtInsert( L, GetItem(S));
    ForEach( @InsertNode);
  end;

destructor tSymbolTable.Done;
  begin
    while Count > 0 do AtFree( Count - 1 );
    if Assigned( Name) then DisposeStr( Name);
    inherited Done;
  end;

procedure tSymbolTable.Store(var S: TStream);
  var
    L: LongInt;
  begin
    {inherited Store(S);}
    {S.Write(SymbolTableType, SizeOf(SymbolTableType));}
    L := Limit;
    S.Write( L, SizeOf( LongInt));
    L := Delta;
    S.Write( L, SizeOf( LongInt));
    L := Count;
    S.Write( L, SizeOf( LongInt));
    S.Write( DataSize, SizeOf( DataSize));
    HasInitOffset := S.GetPos;
    S.Write( HasInit, SizeOf( HasInit));
    for L := 0 to Count - 1 do
      PutItem( S, At( L));
  end;

function tSymbolTable.Compare(Key1, Key2: Pointer): LongInt;
  begin
    {if pString(Key1)^ = pString(Key2)^ then Compare := 0
    else if pString(Key1)^ < pString(Key2)^ then Compare := -1
    else Compare := 1;}
    Compare := LongInt( Key1) - LongInt( Key2);
  end;

function EvaluateFastValue( const Str: String): LongInt;
  var
    L: LongInt;
    I: Integer;
  begin
    L := 0;
    for I := 1 to Length( Str) do
      L := L + Ord( Str[ I]);
    EvaluateFastValue := L;
  end;

function tSymbolTable.KeyOf(Item: Pointer): Pointer;
  begin
    KeyOf := Pointer( pSymbol(Item)^.FastValue);
  end;

procedure tSymbolTable.Insert(Item: Pointer);
  begin
    {inherited Insert( Item);}
    AtInsert( Count, Item);
    pSymbol(Item)^.Owner := @Self;
    InsertToTree( Item);
  end;

function tSymbolTable.Search( const SymbolName: String): Pointer;

  function Test( Item: pSymbol): Boolean; {$IFDEF TP}far;{$ENDIF}
    begin
      Test := Item^.SymbolName^ = SymbolName;
    end;

  var
    Symbol: pSymbol;
    Res: Integer;
    P: Pointer;

  begin
    {for I := 0 to Count - 1 do
      begin
        Item := At(I);
        if (Compare( Key, KeyOf( Item )) = 0) then
          begin
            Index := I;
            Search := True;
            Exit;
          end;
      end;
    Search := False;}
    Symbol := Root;
    P := Pointer( EvaluateFastValue( SymbolName));
    if Assigned( Symbol) then
      while Assigned( Symbol) do
        begin
          Res := Compare( P, Pointer( Symbol^.FastValue));
          if (Res = 0) and (Symbol^.SymbolName^ = SymbolName) then
            begin
              Search := Symbol;
              Exit;
            end
          else if Res < 0 then
            Symbol := Symbol^.Left
          else
            Symbol := Symbol^.Right;
        end
    else
      begin
        Search := FirstThat( @Test);
        Exit;
      end;
    Search := nil;
  end;

function tSymbolTable.GetName: String;
  begin
    if Assigned( Name) then
      GetName := Name^
    else
      GetName := '';
  end;

function tSymbolTable.FindSymbol( const aName: tNameString): pSymbol;
  var
    Symbol: pSymbol;
  begin
    FindSymbol := nil;
    Symbol := Search( aName);
    if Assigned( Symbol) then
      FindSymbol := Symbol
    else if (SymbolTableType = stObjectTable) and Assigned( Owner) and
      Assigned( pObjectDefinition( Owner)^.Ancestor) then
      FindSymbol := pObjectDefinition( Owner)^.Ancestor^.PublicSymbols^.FindSymbol( aName);
  end;

function tSymbolTable.FindWithAlias( const aName: tNameString): pSymbol;
  var
    I: Integer;
    Item: pSymbol;
  begin
    for I := 0 to Count - 1 do
      begin
        Item := At(I);
        if ( (Item^._Type = cFunctionSymbol) and
          ( Assigned(pFunctionSymbol( Item)^.Alias) ) and
          ( pFunctionSymbol( Item)^.Alias^ = aName ) ) then
          begin
            FindWithAlias := Item;
            Exit;
          end;
      end;
    FindWithAlias := nil;
  end;

function tSymbolTable.GetItem(var S: TStream): Pointer;
  var
    Sym: pSymbol;
  begin
    Sym := ReadSymbol( S);
    if Assigned( Sym) then
      begin
        Sym^.Owner := @Self;
        case Sym^._Type of
          cConstSymbol:
            ReadConstValue( S, pConstSymbol( Sym)^.Value);
          {cTypedConstSymbol:
            ReadConstValue( S, pTypedConstSymbol( Sym)^.Value);}
        end;
      end;
    GetItem := Sym;
  end;

procedure tSymbolTable.PutItem(var S: TStream; Item: Pointer);
  begin
    if Assigned( Item) then with pSymbol( Item)^ do
      begin
        S.Write( _Type, SizeOf( _Type));
        Store( S);
        case pSymbol( Item)^._Type of
          cConstSymbol:
            WriteConstValue( S, pConstSymbol( Item)^.Value,
              pConstSymbol( Item)^.ConstType);
          {cTypedConstSymbol:
            WriteConstValue( S, pTypedConstSymbol( Item)^.Value,
              pTypedConstSymbol( Item)^.Definition);}
        end;
      end
  end;

function GetWeight( Symbol: pSymbol): LongInt;
  begin
    if Assigned( Symbol) then
      GetWeight := Symbol^.Weight
    else
      GetWeight := 0;
  end;

procedure ReWeigh( var Symbol: pSymbol);
  var
    L, R: LongInt;
    S: pSymbol;
  begin
    if not Assigned( Symbol) then Exit;
    L := GetWeight( Symbol^.Left);
    R := GetWeight( Symbol^.Right);
    if L > R * 2 + 1 then
      begin
        S := Symbol;
        Symbol := Symbol^.Left;
        S^.Left := Symbol^.Right;
        Symbol^.Right := S;
        S^.Weight := GetWeight( S^.Left) + GetWeight( S^.Right);
        Symbol^.Weight := GetWeight( Symbol^.Left) + GetWeight( Symbol^.Right);
        ReWeigh( Symbol^.Left);
        ReWeigh( Symbol^.Right);
      end
    else if R > L * 2 + 1 then
      begin
        S := Symbol;
        Symbol := Symbol^.Right;
        S^.Right := Symbol^.Left;
        Symbol^.Left := S;
        S^.Weight := GetWeight( S^.Left) + GetWeight( S^.Right);
        Symbol^.Weight := GetWeight( Symbol^.Left) + GetWeight( Symbol^.Right);
        ReWeigh( Symbol^.Left);
        ReWeigh( Symbol^.Right);
      end;
  end;

procedure tSymbolTable.InsertToTree( Item: Pointer);
  var
    Symbol: pSymbol;
    P: Pointer;
  begin
    Symbol := Root;
    P := KeyOf( Item);
    if Assigned( Symbol) then
      begin
        while True do
          begin
            Inc( Symbol^.Weight);
            if Compare( Pointer( Symbol^.FastValue), P) > 0 then
              begin
                if Assigned( Symbol^.Left) then
                  Symbol := Symbol^.Left
                else
                  begin
                    Symbol^.Left := Item;
                    break;
                  end;
              end
            else
              begin
                if Assigned( Symbol^.Right) then
                  Symbol := Symbol^.Right
                else
                  begin
                    Symbol^.Right := Item;
                    break;
                  end;
              end;
          end;
      end
    else
      begin
        Root := Item;
        Root^.Weight := 0;
      end;
    {ReWeigh( Root);}
  end;


constructor tSymbol.Init(const aName: tNameString; anOptions: LongInt);
  begin
    inherited Init;
    _Type := cAbstractSymbol;
    SymbolName := NewStr(aName);
    Options := anOptions;
    Owner := nil;
    isForward := False;
    FastValue := EvaluateFastValue( aName);
  end;

constructor tSymbol.Load(var S: TStream);
  begin
    inherited Init;
    {S.Read(_Type, SizeOf(_Type));}
    _Type := cAbstractSymbol;
    SymbolName := S.ReadStr;
    FastValue := EvaluateFastValue( SymbolName^);
    S.Read( Options, SizeOf( Options));
    Owner := nil;
    isForward := False;
    Left := nil;
    Right := nil;
  end;

destructor tSymbol.Done;
  begin
    if SymbolName <> nil then DisposeStr(SymbolName);
    inherited Done{$IFDEF PPRO}(){$ENDIF};
  end;

procedure tSymbol.Store(var S: TStream);
  begin
    {S.Write(_Type, SizeOf(_Type));}
    S.WriteStr(SymbolName);
    S.Write( Options, SizeOf( Options));
  end;

function tSymbol.Name: tNameString;
  begin
    Name := SymbolName^;
  end;

function tSymbol.AsmName: String;
  begin
    if Assigned( Owner) then
      AsmName := Owner^.GetName + SymbolName^
    else
      AsmName := SymbolName^;
  end;

procedure tSymbol.SetName( const NewName: tNameString);
  begin
    if SymbolName <> nil then DisposeStr(SymbolName);
    SymbolName := NewStr(NewName);
  end;

procedure tSymbol.WriteTo( S: pStream);
  begin
  end;


constructor tProgramSymbol.Init(const aName: tNameString; aSymbolTable: pSymbolTable);
  begin
    inherited Init(aName, 0);
    _Type := cProgramSymbol;
    SymbolTable := aSymbolTable;
  end;


constructor tUnitSymbol.Init(const aName: tNameString;
    aUnitSymbols: pSymbolTable; aLinkFiles: pFileCollection);
  var
    I: tIndex;
    UI: pUnitItem;
  begin
    inherited Init(aName, 0);
    _Type := cUnitSymbol;
    UsedFiles := New( pFileDateCollection, Init( 1, 1));
    UsedUnits := New( pFileCollection, Init( 0, 4));
    LinkFiles := aLinkFiles;
    if Assigned( aUnitSymbols) then
      UnitSymbols := aUnitSymbols
    else
      begin
        UnitSymbols := New( pSymbolTable, Init( stUnitTable, 8, 8));
        UnitSymbols^.Owner := @Self;
        UnitSymbols^.Name := NewStr( aName);
        if Assigned( UnitCollection) then
          if UnitCollection^.Search( @aName, I) then
            begin
              UI := UnitCollection^.At( I);
              UI^.SymbolTable := UnitSymbols;
              UI^.UsedUnits := UsedUnits;
              if Assigned( aLinkFiles) then
                UI^.LinkFiles := aLinkFiles;
            end
          else
            UnitCollection^.Insert( CreateUnitItem( aName, UnitSymbols, UsedUnits, LinkFiles));
      end;
  end;

constructor tUnitSymbol.Load(var S: TStream);
  var
    I: tIndex;
  begin
    inherited Load(S);
    _Type := cUnitSymbol;
    if Assigned( UnitCollection) and
      UnitCollection^.Search( SymbolName, I) then
      begin
        UnitSymbols := pUnitItem( UnitCollection^.At(I))^.SymbolTable;
        if Assigned( UnitSymbols) and (UnitSymbols^.IsCompileInterface) then
          CurCompiler^.Error( erCircularUnitReference, CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol, SymbolName^);
      end
    {else
      ReadUnitFile( SymbolName^);}
  end;

constructor tUnitSymbol.LoadUnit( const aSymbolName: tNameString; const FileName: PathStr);
  var
    I: tIndex;
  begin
    inherited Init( aSymbolName, 0);
    _Type := cUnitSymbol;
    if Assigned( UnitCollection) and
      UnitCollection^.Search( SymbolName, I) then
      begin
        UnitSymbols := pUnitItem( UnitCollection^.At(I))^.SymbolTable;
        if Assigned( UnitSymbols) and (UnitSymbols^.IsCompileInterface) then
          CurCompiler^.Error( erCircularUnitReference, CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol,
            SymbolName^);
      end
    {else
      ReadUnitFile( FileName);}
  end;

destructor tUnitSymbol.Done;
  begin
    {if Assigned( UnitSymbols) then
      Dispose( UnitSymbols, Done);}
    if Assigned( UsedUnits) then
      Dispose( UsedUnits, Done);
    if Assigned( UsedFiles) then
      Dispose( UsedFiles, Done);
    {if Assigned( LinkFiles) then
      Dispose( LinkFiles, Done);}
    inherited Done;
  end;

procedure tUnitSymbol.Store(var S: TStream);
  begin
    inherited Store(S);
  end;

procedure tUnitSymbol.WriteUnit( const FileName: PathStr);
  var
    S: pStream;
  begin
    S := New( pUnitStream, Init( FileName, stCreate));
    {S^.Write( UnitHeader[1], Length( UnitHeader));}
    if S^.Status = stOK then
      begin
        {S^.Put( UsedFiles);
        S^.Put( UsedUnits);
        S^.Put( UnitSymbols);
        S^.Put( LinkFiles);}
        UsedFiles^.Store( S^);
        UsedUnits^.Store( S^);
        UnitSymbols^.Store( S^);
        LinkFiles^.Store( S^);
      end;
    Dispose( S, Done);
  end;

{procedure tUnitSymbol.ReadUnitFile( const FileName: PathStr);
  var
    S: pBufStream;
    Str: String;
    I: Integer;
    FName: PathStr;
  begin
    FName := FileName + UnitExt;
    if not FindFile( FileName + UnitExt, FName,
      UnitSearchPath) then
      CurCompiler^.Error( erFileNotFound, CurCompiler^.Files^.PrevLine,
        CurCompiler^.Files^.PrevCol, FileName + UnitExt);
    S := New( pUnitStream, Init( FName, stOpenRead));
    if S^.Status <> stOK then
      CurCompiler^.Error( erFileNotFound,
        CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol, FName);
    S^.Read( Str[1], Length( UnitHeader));
    Str[0] := UnitHeader[0];
    UnitSymbols := nil;
    if Str = UnitHeader then
      if S^.Status = stOK then
        begin
          UsedFiles := pFileDateCollection( S^.Get);
          UsedUnits := pFileCollection( S^.Get);
          UnitSymbols := pSymbolTable( S^.Get);
          LinkFiles := pFileCollection( S^.Get);
          UnitSymbols^.SymbolTableType := stUnitTable;
          UnitSymbols^.Name := NewStr( SymbolName^);
          UnitSymbols^.Owner := @Self;
          if Assigned( UnitCollection) then
            UnitCollection^.Insert( CreateUnitItem( SymbolName^, UnitSymbols, UsedUnits, LinkFiles));
          for I := 0 to UnitSymbols^.Count - 1 do
            ResolveDefinitions( UnitSymbols^.At(I), UnitSymbols);
        end;
    if not Assigned( UnitSymbols) then
      CurCompiler^.Error( erUnitFileFormatError,
        CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol, FName);
    Dispose( S, Done);
  end;}


constructor tFunctionSymbol.Init(const aName: tNameString; _IsMain: Boolean; anOptions: LongInt);
  begin
    inherited Init(aName, anOptions);
    _Type := cFunctionSymbol;
    IsMain := _IsMain;
  end;

destructor tFunctionSymbol.Done;
  begin
    {if Assigned( NextOverloaded) then
      Dispose( NextOverloaded, Done);}
{writeln( symbolname^, assigned( definition^.objectdef): 6);}
    {if Assigned( Definition) then
      Definition^.DisposeLocalSymbols;}
    if Assigned( _AsmName) then
      DisposeStr( _AsmName);
    if Assigned( Alias) then
      DisposeStr( Alias);
    inherited Done;
  end;

constructor tFunctionSymbol.Load(var S: TStream);
  var
    B: Boolean;
  begin
    inherited Load( S);
    _Type := cFunctionSymbol;
    S.Read( IsMain, SizeOf( IsMain));
    _AsmName := S.ReadStr;
    S.Read( B, SizeOf( B));
    if B then Alias := S.ReadStr;
    {Definition := pFunctionDefinition( S.Get);}
    Definition := pFunctionDefinition( ReadDefinition( S, True));
    S.Read( B, SizeOf( B));
    if B then
      NextOverLoaded := pFunctionSymbol( Read_Symbol(S));
  end;

procedure tFunctionSymbol.Store(var S: TStream);
  var
    B: Boolean;
    L: LongInt;
    Str: String;
  begin
    inherited Store( S);
    S.Write( IsMain, SizeOf( IsMain));
    Str := AsmName{$IFDEF PPRO}(){$ENDIF};
    S.WriteStr( @Str);
    B := Assigned( Alias);
    S.Write( B, SizeOf( B));
    if B then S.WriteStr( Alias);
    {S.Put( Definition);}
    Definition^.Store( S);
    B := Assigned( NextOverloaded);
    S.Write( B, SizeOf( B));
    if B then
      begin
        {S.Write( NextOverloaded^._Type, SizeOf( _Type));
        NextOverloaded^.Store( S);}
        Write_Symbol( S, NextOverloaded);
        L := -1;
        S.Write( L, SizeOf( L));
      end;
  end;

procedure tFunctionSymbol.WriteTo( S: pStream);
  var
    Str: String;
  begin
    if Assigned( Definition) then
      begin
        if Definition^.ProcOptions and poExternal <> 0 then
          Exit;
        if IsMain then
          begin
            Str := _Start_ + _EOL_;
            S^.Write( Str[1], Length(Str));
          end;
        Str := AsmName + ' ' + _Proc_ + ' ' + _EOL_;
        S^.Write( Str[1], Length(Str));
        Definition^.WriteTo( S);
        if _EndP_ <> '' then
          Str := AsmName + ' ENDP' + _EOL_
        else
          Str := '; ' + AsmName + _EOL_;
        S^.Write( Str[1], Length(Str));
      end;
  end;

function tFunctionSymbol.AsmName: String;
  var
    Prefix: String;
  begin
    if Assigned( _AsmName) then
      begin
        AsmName := _AsmName^;
        Exit;
      end;
    if Assigned( Alias) then
      begin
        AsmName := Alias^;
        Exit;
      end;
    Prefix := '';
    if Assigned( Owner) and not IsMain then
    case Owner^.SymbolTableType of
      stGlobalTable:
        if not IsMain then
          Prefix := '_';
      stUnitTable:
        if not IsMain then
          Prefix := 'U_' + Owner^.Name^ + '$$';
      else
        Prefix := Owner^.GetName;
    end;
    AsmName := Prefix + Name +
      Definition^.GetPostfix;
  end;


constructor tOperatorSymbol.Init( aOperator: tPasOperators; anOptions: LongInt);
  begin
    inherited Init( OperatorNames[aOperator], False, anOptions);
    _Type := cOperatorSymbol;
    _Operator := aOperator;
  end;

constructor tOperatorSymbol.Load(var S: TStream);
  begin
    inherited Load( S);
    _Type := cOperatorSymbol;
    S.Read( _Operator, SizeOf( _Operator));
  end;

procedure tOperatorSymbol.Store(var S: TStream);
  begin
    inherited Store( S);
    S.Write( _Operator, SizeOf( _Operator));
  end;


constructor tTypeSymbol.Init(const aName: tNameString; aDefinition: pDefinition; anOptions: LongInt);
  begin
    inherited Init(aName, anOptions);
    _Type := cTypeSymbol;
    Definition := aDefinition;
    IsOwner := False;
    if Assigned( Definition) and not Assigned( Definition^.Symbol) then
      begin
        Definition^.Symbol := @Self;
        IsOwner := True;
      end;
  end;

destructor tTypeSymbol.Done;
  begin
    {if Assigned( Definition) and (Definition^.Symbol = @Self) then
      Dispose( Definition, Done);}
    inherited Done;
  end;

constructor tTypeSymbol.Load(var S: TStream);
  begin
    inherited Load( S);
    _Type := cTypeSymbol;
    S.Read( IsOwner, SizeOf( IsOwner));
    Definition := ReadDefinition( S, IsOwner);
    if IsOwner then
      Definition^.Symbol := @Self;
  end;

procedure tTypeSymbol.Store(var S: TStream);
  begin
    inherited Store( S);
    S.Write( IsOwner, SizeOf( IsOwner));
    WriteDefinition( S, Definition, IsOwner);
  end;


constructor tConstSymbol.Init(const aName: tNameString; ValType: Integer;
    var aValue; aType: pDefinition; anOptions: LongInt);
  begin
    inherited Init(aName, anOptions);
    _Type := cConstSymbol;
    Value.ValueType := ValType;
    case ValType of
      cvStringValue:
        Value.StringValue := NewStr( pString(aValue)^);
      cvSetValue:
        begin
          GetMem( Value.InfoPtr, SizeOf( tByteSet) );
          Move( Value.InfoPtr^, aValue, SizeOf( tByteSet) );
        end;
      cvAddressValue:
        Value.InfoPtr := Pointer( aValue);
      cvRealValue:
        Value.RealValue := Extended( aValue);
      else
        Value.IntValue := LongInt(aValue)
    end;
    ConstType := aType;
  end;

destructor tConstSymbol.Done;
  begin
    if Assigned( ConstType) then
      begin
        case ConstType^.DefType of
          cStringDefinition:
            DisposeStr( Value.StringValue);
          cSetDefinition:
            FreeMem( Value.InfoPtr, SizeOf( tByteSet));
          cPointerDefinition:
            Dispose( pPointerValue( Value.InfoPtr));
        end;
        {if Assigned( ConstType) and not Assigned( ConstType^.Symbol) then
          Dispose( ConstType, Done);}
      end;
    inherited Done;
  end;

constructor tConstSymbol.Load(var S: TStream);
  begin
    inherited Load( S);
    _Type := cConstSymbol;
    ConstType := ReadDefinition( S, False);
  end;

procedure tConstSymbol.Store(var S: TStream);
  begin
    inherited Store( S);
    WriteDefinition( S, ConstType, False);
  end;


constructor tLabelSymbol.Init(const aName: tNameString; anOptions: LongInt);
  begin
    inherited Init(aName, anOptions);
    _Type := cLabelSymbol;
  end;

function tLabelSymbol.AsmName: String;
  var
    Prefix: String;
  begin
    Prefix := '';
    case Owner^.SymbolTableType of
      stGlobalTable:
        begin
          Prefix := '_$LABEL$';
        end;
      stUnitTable:
        begin
          Prefix := 'U$$' + Owner^.Name^ + '$LABEL$';
        end;
      else
        Prefix := Owner^.Name^ + '$LABEL$';
    end;
    AsmName := Prefix + Name{$IFDEF PPRO}(){$ENDIF};
  end;


constructor tVariableSymbol.Init(const aName: tNameString; aTypeDef: pDefinition; aVarType: tVariableType; anOptions: LongInt);
  begin
    inherited Init(aName, anOptions);
    _Type := cVariableSymbol;
    Definition := aTypeDef;
    VarType := aVarType;
    IsOwner := False;
    if Assigned( Definition) and not Assigned( Definition^.Symbol) then
      begin
        Definition^.Symbol := @Self;
        IsOwner := True;
      end;
  end;

destructor tVariableSymbol.Done;
  begin
    {if Assigned( Definition) and (IsOwner) then
      Dispose( Definition, Done);}
    inherited Done{$IFDEF PPRO}(){$ENDIF};
  end;

constructor tVariableSymbol.Load(var S: TStream);
  begin
    inherited Load( S);
    _Type := cVariableSymbol;
    S.Read( VarType, SizeOf( VarType));
    S.Read( IsOwner, SizeOf( IsOwner));
    S.Read( Offset, SizeOf( Offset));
    Definition := ReadDefinition( S, IsOwner);
  end;

procedure tVariableSymbol.Store(var S: TStream);
  begin
    inherited Store( S);
    S.Write( VarType, SizeOf( VarType));
    S.Write( IsOwner, SizeOf( IsOwner));
    S.Write( Offset, SizeOf( Offset));
    WriteDefinition( S, Definition, IsOwner);
  end;

function tVariableSymbol.AsmName: String;
  var
    Prefix: String;
  begin
    Prefix := '';
    {if not Assigned( Owner) then ;}
    case Owner^.SymbolTableType of
      stGlobalTable:
        begin
          Prefix := '_';
        end;
      stUnitTable:
        begin
          Prefix := 'U$$' + Owner^.Name^ + '$$';
        end;
    end;
    AsmName := Prefix + Name{$IFDEF PPRO}(){$ENDIF};
  end;

function tVariableSymbol.Size: LongInt;
  begin
    Size := Definition^.GetSize{$IFDEF PPRO}(){$ENDIF};
  end;

function tVariableSymbol.IsGlobal: Boolean;
  begin
    IsGlobal := VarType = cvtGlobal;
  end;

procedure tVariableSymbol.WriteTo( S: pStream);
  var
    Str: String;
  begin
    Str := AsmName + ' ' + _ResB_ + ' ' +
      ToStr( Size) + ' ' + _DUP_ + _EOL_;
    S^.Write( Str[1], Length(Str));
  end;


constructor tTypedConstSymbol.Init(const aName: tNameString; aTypeDef: pDefinition; anOptions: LongInt);
  begin
    inherited Init(aName, aTypeDef, cvtGlobal, anOptions);
    _Type := cTypedConstSymbol;
    {if Assigned( aTypeDef) then
      aTypeDef^.Symbol := @Self;}
  end;

destructor tTypedConstSymbol.Done;
  begin
    {Tools.DisposeValue( Value.InfoPtr, Definition);
    case Definition^.DefType of
      cStringDefinition:
        DisposeStr( Value.StringValue);
      cSetDefinition,
      cArrayDefinition,
      cRecordDefinition:
        FreeMem( Value.InfoPtr, Definition^.GetSize);
    end;}
    inherited Done;
  end;

constructor tTypedConstSymbol.Load(var S: TStream);
  begin
    inherited Load( S);
    _Type := cTypedConstSymbol;
  end;

procedure tTypedConstSymbol.Store(var S: TStream);
  begin
    inherited Store( S);
  end;

procedure tTypedConstSymbol.WriteTo( S: pStream);
  var
    Str: String;
  begin
    Str := AsmName;
    S^.Write( Str[1], Length(Str));
    WriteValue( S);
  end;


procedure WriteVal( S: pStream; Definition: pDefinition; var Value: tValue); forward;

procedure WriteStringValue( Str: PString; S: pStream; Def: pStringDefinition);
  var
    I: LongInt;
    St, St2: String;
  begin
    I := 0;
    if Assigned( Str) then
      begin
    St := ' ' + _DB_ + ' ' + ToStr( Byte( Str^[0]));
    S^.Write( St[1], Byte( St[0]) );
    St := '';
    for I := 1 to Length( Str^) do
      begin
        if I > Def^.Length then break;
        if (Str^[I] in [#0..#31, #255, '''']) then
          begin
            if St <> '' then
              begin
                St := ',''' + St + '''';
                S^.Write( St[1], Byte( St[0]) );
              end;
            St := ',' + ToStr( Byte(Str^[I]));
            S^.Write( St[1], Length(St));
            St := '';
          end
        else
          St := St + Str^[I];
        {I := Length( Str^);}
        if I = Length( Str^) then break;
      end;
    if St <> '' then
      St := ',''' + St + '''';
      end
    else
      St := ' ' + _DB_ + ' 0';
    St := St + _EOL_;
    S^.Write( St[1], Byte( St[0]) );
    if I < Def^.Length then
      begin
        St := ' ' + _ResB_ + ' ' + ToStr( Def^.Length - I) + ' ' + _DUP_ + _EOL_;
        S^.Write( St[1], Length( St));
      end;
  end;

procedure WriteRealValue( Value: Extended; S: pStream; RealType: tRealType);
  var
    St: String;
    Sngl: Single;
    Dbl: Double;
  begin
    {Str( Value, St);}
    case RealType of
      crtSingle:
        begin
          Sngl := Value;
          St := ' ' +  _DB_ + ' ' + ToStr( pByteArray( @Sngl)^[ 0]) +',' +
            ToStr( pByteArray( @Sngl)^[ 1]) + ',' +
            ToStr( pByteArray( @Sngl)^[ 2]) + ',' +
            ToStr( pByteArray( @Sngl)^[ 3]);
        end;
      crtDouble:
        {ST := ' ' + _DQ_ + ' ' + St;}
        begin
          Dbl := Value;
          St := ' ' +  _DB_ + ' ' + ToStr( pByteArray( @Dbl)^[ 0]) +',' +
            ToStr( pByteArray( @Dbl)^[ 1]) + ',' +
            ToStr( pByteArray( @Dbl)^[ 2]) + ',' +
            ToStr( pByteArray( @Dbl)^[ 3]) + ',' +
            ToStr( pByteArray( @Dbl)^[ 4]) + ',' +
            ToStr( pByteArray( @Dbl)^[ 5]) + ',' +
            ToStr( pByteArray( @Dbl)^[ 6]) + ',' +
            ToStr( pByteArray( @Dbl)^[ 7]);
        end;
      crtExtended:
        {St := ' ' + _DT_ + ' ' + St;}
          St := ' ' +  _DB_ + ' ' + ToStr( pByteArray( @Value)^[ 0]) +',' +
            ToStr( pByteArray( @Value)^[ 1]) + ',' +
            ToStr( pByteArray( @Value)^[ 2]) + ',' +
            ToStr( pByteArray( @Value)^[ 3]) + ',' +
            ToStr( pByteArray( @Value)^[ 4]) + ',' +
            ToStr( pByteArray( @Value)^[ 5]) + ',' +
            ToStr( pByteArray( @Value)^[ 6]) + ',' +
            ToStr( pByteArray( @Value)^[ 7]) + ',' +
            ToStr( pByteArray( @Value)^[ 8]) + ',' +
            ToStr( pByteArray( @Value)^[ 9]);
    end;
    St := St + _EOL_;
    S^.Write( St[1] , Byte(St[0]) );
  end;

procedure WritePointerValue( Value: pPointerValue; S: pStream);
  var
    St: String;
  begin
    if Assigned( Value) then
      begin
        St := ' ' + _DD_ + ' ';
        if Assigned( Value^.Symbol) then
          begin
            St := St + _Offset_ + ' ' + Value^.Symbol^.AsmName;
            if Value^.Offset > 0 then
              St := St + ' + ' + ToStr( Value^.Offset)
            else if Value^.Offset < 0 then
              St := St + ' - ' + ToStr( -Value^.Offset);
          end
        else if Assigned( Value^.AsmLabel) then
          begin
            St := St + _Offset_+ ' ' + Value^.AsmLabel^;
            if Value^.Offset > 0 then
              St := St + ' + ' + ToStr( Value^.Offset)
            else if Value^.Offset < 0 then
              St := St + ' - ' + ToStr( -Value^.Offset);
          end
        else
          St := St + ToStr( Value^.Offset);
        {Dispose( Value);}
      end
    else
      St := ' ' + _DD_ + ' ?';
    St := St + _EOL_;
    S^.Write( St[1], Byte( St[0]));
  end;

procedure WriteRecordValue( S: pStream; Rec: pRecordDefinition; Value: pValueArray);
  var
    L: LongInt;
  begin
    {Rec^.Fields^.ForEach( @WriteFieldValue);}
    for L := 0 to Rec^.GetCount - 1 do
      WriteVal( S, pVariableSymbol( Rec^.Fields^.At( L))^.Definition, Value^[ L]);
  end;

procedure WriteArrayValue( S: pStream; Arr: pArrayDefinition; Value: pValueArray);
  var
    L, Count: LongInt;
  begin
    Count := Arr^.GetCount;
    for L := 0 to Count - 1 do
      WriteVal( S, Arr^.ComponentDef,
        Value^[ L] );
  end;

procedure WriteCharArrayValue( Value: pByteArray; Count: LongInt; S: pStream);
  var
    I: LongInt;
    St: String;
  begin
    St := '';
    I := 0;
    while I < Count do
      begin
        if (I < Count) and (Length( St) < 120) and
          (Value^[ I] >= 32) and (Value^[I] < 255) then
          begin
            St := St + '"';
            repeat
              St := St + Chr( Value^[ I]);
              Inc( I);
            until (I >= Count) or (Length( St) >= 120) or
              (Value^[ I] < 32) or (Value^[I] = 255) or (Value^[I] = Byte('"'));
            St := St + '"';
          end;
        while (I < Count) and (Length( St) < 120) and
          (Value^[ I] in [0..31, 255, Ord( '"')]) do
          begin
            if Length( St) <> 0 then
              St := St + ',';
            St := St + ToStr( Value^[ I]);
            Inc( I);
          end;
        if St <> '' then
          begin
            St := ' ' + _DB_ + ' ' + St + _EOL_;
            S^.Write( St[ 1], Length( St));
            St := '';
          end;
      end;
  end;

procedure WriteASCIIZValue( Value: pString; S: pStream; ConstType: LongInt);
  var
    I: LongInt;
    Count: LongInt;
    St: String;
    pS: pString;
  begin
    if ConstType = cvASCIIZValue then
      begin
        pS := NewStr( CurCompiler^.CreateLabel);
        St := ' ' + _DD_ + ' ' + _Offset_ + ' ' + pS^ + _EOL_;
        S^.Write( St[ 1], Length( St));
        S^.Write( pS^[ 1], Length( pS^));
        DisposeStr( pS);
      end;
    St := '';
    I := 1;
    if Assigned( Value) then
      Count := Length( Value^)
    else
      Count := 0;
    while I <= Count do
      begin
        if (I <= Count) and (Length( St) < 120) and
          (Value^[ I] >= #32) and (Value^[I] < #255) then
          begin
            St := St + '"';
            repeat
              St := St + Value^[ I];
              Inc( I);
            until (I > Count) or (Length( St) >= 120) or
              (Value^[ I] < #32) or (Value^[I] = #255) or (Value^[I] = '"');
            St := St + '"';
          end;
        while (I <= Count) and (Length( St) < 120) and
          (Value^[ I] in [#0..#31, #255, '"']) do
          begin
            if Length( St) <> 0 then
              St := St + ',';
            St := St + ToStr( Ord( Value^[ I]));
            Inc( I);
          end;
        if St <> '' then
          begin
            St := ' ' + _DB_ + ' ' + St + _EOL_;
            S^.Write( St[ 1], Length( St));
            St := '';
          end;
      end;
    St := ' ' + _DB_ + ' 0'#13#10;
    S^.Write( St[ 1], Length( St));
  end;

procedure WriteVal( S: pStream; Definition: pDefinition; var Value: tValue);
  var
    St: String;
    I: LongInt;
  begin
    St := '';
    case Value.ValueType Of
      cvOrdinalValue:
        begin
          case Definition^.GetSize of
            1:
              begin
                Str( Byte( Value.IntValue), St);
                St := ' ' + _DB_ + ' ' + St + _EOL_;
              end;
            2:
              begin
                Str( Word( Value.IntValue), St);
                St := ' ' + _DW_ + ' ' + St + _EOL_;
              end;
            4:
              begin
                Str( LongInt( Value.IntValue), St);
                St := ' ' + _DD_ + ' ' + St + _EOL_;
              end;
          end;
        end;
      cvStringValue:
        WriteStringValue( Value.StringValue, S, pStringDefinition( Definition));
      cvRealValue:
        WriteRealValue( Value.RealValue, S,
          pRealDefinition( Definition)^.RealType);
      cvAddressValue,
      cvProceduralValue:
        WritePointerValue( Value.InfoPtr, S);
      cvArrayValue:
        WriteArrayValue( S, pArrayDefinition( Definition), Value.InfoPtr);
      cvRecordValue:
        WriteRecordValue( S, pRecordDefinition( Definition), Value.InfoPtr);
      cvSetValue:
        begin
          for I := 0 to Definition^.GetSize - 1 do
            begin
              St := ' ' + _DB_ + ' ' + ToStr( pByteArray( Value.InfoPtr)^[I]) + _EOL_;
              S^.Write( St[1], Length(St));
            end;
          St := '';
        end;
      cvCharArrayValue:
        WriteCharArrayValue( Value.InfoPtr,
          pArrayDefinition( Definition)^.GetCount, S);
      cvASCIIZValue,
      cvPCharValue:
        WriteASCIIZValue( Value.InfoPtr, S, Value.ValueType);
    end;
    if St <> '' then
      S^.Write( St[1], Length(St));
  end;

procedure tTypedConstSymbol.WriteValue( S: pStream);
  {var
    P: Pointer;}
  begin
    {case Definition^.DefType of
      cOrdDefinition,
      cUserOrdDefinition,
      cBooleanDefinition,
      cPointerDefinition,
      cFunctionTypeDefinition,
      cRealDefinition:
        P := @Value.IntValue;
      cStringDefinition:
        P := Value.StringValue;
      else
        P := Value.InfoPtr;
    end;}
    WriteVal( S, Definition, Value);
  end;

procedure tTypedConstSymbol.DisposeValue;
  begin
    if Assigned( Definition) then
      begin
        Tools.DisposeValue( Value, Definition);
        {case Definition^.DefType of
          cOrdDefinition,
          cUserOrdDefinition,
          cBooleanDefinition,
          cRealDefinition:;

          cFunctionTypeDefinition,
          cPointerDefinition:
            if Assigned( Value.InfoPtr) then
              Dispose( pPointerValue( Value.InfoPtr) );
          cStringDefinition:
            if Assigned( Value.StringValue) then DisposeStr( Value.StringValue);
          cSetDefinition:
            if Assigned( Value.InfoPtr) then
              FreeMem( Value.InfoPtr, 32);
          else
            if Assigned( Value.InfoPtr) then
              FreeMem( Value.InfoPtr, Definition^.GetSize);
        end;}
      end;
  end;

function tTypedConstSymbol.AsmName: String;
  var
    Prefix: String;
  begin
    Prefix := 'TC_';
    {if not Assigned( Owner) then ;}
    case Owner^.SymbolTableType of
      stGlobalTable:
        begin
          Prefix := Prefix + '_';
        end;
      stUnitTable:
        begin
          Prefix := Prefix + 'U_' + Owner^.Name^ + '_';
        end;
    end;
    AsmName := Prefix + Name;
  end;


{--- tAbsoluteSymbol ---}
constructor tAbsoluteSymbol.Init(const aName: tNameString; aTypeDef: pDefinition;
      aVarType: tVariableType; anOptions: LongInt;
      AbsType: tAbsoluteType; Ref: pVariableSymbol);
  begin
    inherited Init( aName, aTypeDef, aVarType, anOptions);
    _Type := cAbsoluteSymbol;
    AbsoluteType := AbsType;
    Reference := Ref;
  end;

constructor tAbsoluteSymbol.Load(var S: TStream);
  begin
    inherited Load( S);
    S.Read( AbsoluteType, SizeOf( AbsoluteType));
    if AbsoluteType = catAddress then
      S.Read( Reference, SizeOf( Reference))
    else
      Reference := pVariableSymbol( Read_Symbol( S));;
  end;

procedure tAbsoluteSymbol.Store(var S: TStream);
  var
    L: LongInt;
  begin
    inherited Store( S);
    S.Write( AbsoluteType, SizeOf( AbsoluteType));
    if AbsoluteType = catAddress then
      S.Write( Reference, SizeOf( Reference))
    else
      begin
        Write_Symbol( S, Reference);
        L := -1;
        S.Write( L, SizeOf( L));
      end;
  end;


{--- tMacroSymbol ---}
constructor tMacroSymbol.Init(const aName: tNameString);
  begin
    inherited Init(aName, 0);
    _Type := cMacroSymbol;
  end;


{--- tUserOrdSymbol ---}
constructor tUserOrdSymbol.Init( const aName: tNameString; aValue: LongInt; Def: pUserOrdDefinition; anOptions: LongInt);
  begin
    inherited Init( aName, anOptions);
    _Type := cUserOrdSymbol;
    Definition := Def;
    Value := aValue;
  end;

constructor tUserOrdSymbol.Load(var S: TStream);
  begin
    inherited Load( S);
    _Type := cUserOrdSymbol;
    S.Read( Value, SizeOf( Value));
    Definition := pUserOrdDefinition( ReadDefinition( S, False));
  end;

procedure tUserOrdSymbol.Store(var S: TStream);
  begin
    inherited Store( S);
    S.Write( Value, SizeOf( Value));
    WriteDefinition( S, Definition, False);
  end;


{ tSystemSymbol }
constructor tSystemSymbol.Init( const aName: tNameString; SysType: tSystemSymbolType; anOptions: LongInt);
  begin
    inherited Init( aName, anOptions);
    _Type := cSystemSymbol;
    SystemType := SysType;
  end;

constructor tSystemSymbol.Load(var S: TStream);
  begin
    inherited Load( S);
    _Type := cSystemSymbol;
    S.Read( SystemType, SizeOf( SystemType));
  end;

procedure tSystemSymbol.Store(var S: TStream);
  begin
    inherited Store( S);
    S.Write( SystemType, SizeOf( SystemType));
  end;


{ tDefinition }
constructor tDefinition.Init;
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    DefType := cAbstractDefinition;
    Self.NextDefinition := DefinitionList;
    DefinitionList := @Self;
  end;

constructor tDefinition.Load(var S: TStream);
  begin
    inherited Init;
    Self.NextDefinition := DefinitionList;
    DefinitionList := @Self;
    S.Read( DefType, SizeOf(DefType));
  end;

procedure tDefinition.Store(var S: TStream);
  begin
    S.Write( DefType, SizeOf(DefType));
  end;

function tDefinition.GetSize: LongInt;
  begin
    GetSize := -1;
  end;

function tDefinition.GetName: String;
  begin
    if Assigned( Symbol) then
      GetName := Symbol^.SymbolName^
    else
      GetName := '';
  end;


constructor tAbstractFunctionDefinition.Init( Result: pDefinition);
  begin
    inherited Init;
    ResType := Result;
    {InitParameters;}
  end;

destructor tAbstractFunctionDefinition.Done;
  begin
    DisposeDefCollection( ParamColl);
    inherited Done;
  end;

constructor tAbstractFunctionDefinition.Load(var S: TStream);
  var
    VType: tVariableType;
    DefColl: ^pDefCollection;
  begin
    inherited Load( S);
    ParamColl := nil;
    DefColl := @ParamColl;
    S.Read( VType, SizeOf( tVariableType));
    while VType in [cvtParam, cvtVarParam, cvtConstParam, cvtStringParam] do
      begin
        if VType <> cvtUnknown then
          begin
            New( DefColl^);
            DefColl^^.ParamType := VType;
            DefColl^^.Definition := ReadDefinition( S, False);
            DefColl^^.Next := nil;
            DefColl := @(DefColl^^.Next);
          end;
        S.Read( VType, SizeOf( tVariableType));
      end;
    S.Read( ParamSize, SizeOf( ParamSize));
    S.Read( Options, SizeOf( Options));
    S.Read( CallType, SizeOf( CallType));
    ResType := ReadDefinition( S, False);
  end;

procedure tAbstractFunctionDefinition.Store(var S: TStream);
  var
    DefColl: pDefCollection;
    VType: tVariableType;
  begin
    inherited Store( S);
    DefColl := ParamColl;
    while Assigned( DefColl) do
      begin
        S.Write( DefColl^.ParamType, SizeOf( tVariableType));
        WriteDefinition( S, DefColl^.Definition, False);
        DefColl := DefColl^.Next;
      end;
    VType := cvtUnknown;
    S.Write( VType, SizeOf( VType));
    S.Write( ParamSize, SizeOf( ParamSize));
    S.Write( Options, SizeOf( Options));
    S.Write( CallType, SizeOf( CallType));
    WriteDefinition( S, ResType, False);
  end;

procedure tFunctionDefinition.SetCallType( NewCallType: tCallType);
  var
    BegOfs: LongInt;

  procedure SetOffset( P: pVariableSymbol); {$IFDEF TP} far;{$ENDIF}
    var
      L: LongInt;
    begin
      if (P^._Type = cVariableSymbol) and
        (P^.VarType in [cvtVarParam, cvtParam, cvtConstParam, cvtStringParam]) then
        begin
          if Assigned( ResType) and
            (P^.SymbolName^ = FuncResultName) then Exit;
          if Assigned( ObjectDef) and
            (P^.SymbolName^ = SelfName) then Exit;
          L := (P^.Definition^.GetSize + 3) and not 3;
          P^.Offset := ParamSize - L - P^.Offset + BegOfs * 2;
        end;
    end;  

  begin
    if (CallType = cctDefault) and
      ((NewCallType = cctStdCall) or (NewCallType = cctCDecl)) then
      begin
        if LexLevel > 1 then
          BegOfs := 12
        else
          BegOfs := 8;
        if Assigned( ResType) and
          not (ResType^.DefType in [ cOrdDefinition, cUserOrdDefinition, cBooleanDefinition,
            cPointerDefinition, cRealDefinition]) then
          Dec( BegOfs, 2);
        if Assigned( ObjectDef) then
          Dec( BegOfs, 2);
        LocalSymbols^.ForEach( @SetOffset);
      end;
    CallType := NewCallType;
  end;


constructor tFunctionTypeDefinition.Init( Result: pDefinition);
  begin
    inherited Init( Result);
    DefType := cFunctionTypeDefinition;
  end;

function tFunctionTypeDefinition.GetSize: LongInt;
  begin
    GetSize := 4;
  end;


function tFunctionDefinition.GetPostfix: String;
  var
    Str: String;
    DefColl: pDefCollection;

  procedure GetParamName( Def: pDefinition); {$IFDEF TP}far;{$ENDIF}
    begin
      if Assigned( Def) then
        begin
          Str := Str + '$$' + Def^.GetName;
        end;
    end;

  begin
    Str := '';
    DefColl := ParamColl;
    while Assigned( DefColl) do
      begin
        GetParamName( DefColl^.Definition);
        DefColl := DefColl^.Next;
      end;
    GetPostfix := Str;
  end;


constructor tFunctionDefinition.Init( Result: pDefinition; aLevel: Byte; anObjectDef: pObjectDefinition);
  begin
    inherited Init( Result);
    DefType := cFunctionDefinition;
    LexLevel := aLevel;
    ObjectDef := anObjectDef;
    InitLocalSymbols;
  end;

constructor tFunctionDefinition.Load( var S: tStream);
  begin
    inherited Load( S);
    S.Read( ProcOptions, SizeOf( ProcOptions));
    S.Read( VirtualIndex, SizeOf( VirtualIndex));
    ObjectDef := pObjectDefinition( ReadDefinition( S, False));
  end;

procedure tFunctionDefinition.Store( var S: tStream);
  begin
    inherited Store( S);
    S.Write( ProcOptions, SizeOf( ProcOptions));
    S.Write( VirtualIndex, SizeOf( VirtualIndex));
    WriteDefinition( S, ObjectDef, False);
  end;

destructor tFunctionDefinition.Done;
  begin
    {if Assigned( LocalSymbols) then
      Dispose( LocalSymbols, Done);}
    if Assigned( Code) then
      Dispose( pCodeTree(Code), Done);
    inherited Done;
  end;

procedure tFunctionDefinition.InitLocalSymbols;
  begin
    LocalSymbols := New(pSymbolTable, Init(stLocalTable, 4, 4));
    LocalSymbols^.Owner := @Self;
  end;

procedure tFunctionDefinition.GenEntryExit( AsmProc: Pointer);
  var
    Ref: tReference;
    I: tIndex;
    Sym: pVariableSymbol;
    Size: LongInt;
  begin
    with pProcAsm(AsmProc)^ do
      begin
        Size := LocalSymbols^.DataSize + TempSize;
        if Size and 3 <> 0 then Size := Size and not 3 + 4;
        if Size > 0 then
          Insert( New( pAsmInstruction, Create_Reg_Const(
            caiSUB, crESP, Size)));
        Insert( New( pAsmInstruction, Create_Reg_Reg(
          caiMOV, crEBP, crESP)));
        Insert( New( pAsmInstruction, Create_Reg(
          caiPUSH, crEBP)));

        if Assigned( ResType) and (ResType^.DefType <> cAbstractDefinition) then
          case ResType^.DefType of
            cOrdDefinition,
            cUserOrdDefinition,
            cBooleanDefinition,
            cPointerDefinition:
              begin
                Sym := LocalSymbols^.Search( FuncResultName);
                if not Sym^.IsRegisterable then
                  begin
                    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                      Sym^.Offset, nil,
                      Tools.GetSize( ResType^.GetSize), Ref);
                    if ResType^.GetSize = 4 then
                      Concat( New( pAsmInstruction, Create_Reg_Ref(
                        caiMOV, crEAX, Ref)))
                    else
                      Concat( New( pAsmInstruction, Create_Reg_Ref(
                        caiMOVSX, crEAX, Ref)));
                  end
                else
                  begin
                  end;
              end;
            cRealDefinition:
              begin
                Sym := LocalSymbols^.Search( FuncResultName);
                if not Sym^.IsRegisterable then
                  begin
                    CreateReference( crDefaultSeg, crEBP, crNoRegister, 1,
                      Sym^.Offset, nil, Tools.GetSize( ResType^.GetSize{$IFDEF PPRO}(){$ENDIF}), Ref);
                    Concat( New( pAsmInstruction, Create_Ref(
                        caiFLD, Ref)));
                  end;
              end;
          end;
        Concat( New( pAsmInstruction, Create_Reg_Reg(
          caiMOV, crESP, crEBP)));
        Concat( New( pAsmInstruction, Create_Reg(
          caiPOP, crEBP)));
        if CallType <> cctCDecl then
          Concat( New( pAsmInstruction, Create_Const(
            caiRET, ParamSize)))
        else
          Concat( New( pAsmInstruction, Create(
            caiRET)));
      end;
  end;

procedure tFunctionDefinition.WriteTo( S: pStream);
  var
    AsmProc: pProcAsm;

  begin
    if Assigned( Symbol) then
      if not pFunctionSymbol(Symbol)^.IsMain then
        LocalSize := LocalSymbols^.DataSize;
    if not Assigned( Code) then
      CurCompiler^.Error( erUndefinedForward, CurCompiler^.Files^.PrevLine,
        CurCompiler^.Files^.PrevCol, Symbol^.SymbolName^);
    if not Assigned( Code) then
      CurCompiler^.Error( erInternalError, CurCompiler^.Files^.PrevLine,
    CurCompiler^.Files^.PrevCol, Symbol^.Name);
    AsmProc := GenerateFlatCode( pCodeTree(Code), LexLevel, LocalSize);
    GenEntryExit( AsmProc);
    AsmProc^.WriteTo(S);
    Dispose( AsmProc, Done);

    Dispose( pCodeTree(Code), Done);
    Code := nil;
  end;

procedure tFunctionDefinition.DisposeLocalSymbols;
  begin
    Dispose( LocalSymbols, Done);
    LocalSymbols := nil;
  end;


constructor tMainFunctionDefinition.Init;
  begin
    inherited Init(nil, 0, nil);
  end;

constructor tMainFunctionDefinition.Load(var S: TStream);
  begin
    inherited Load( S);
  end;

procedure tMainFunctionDefinition.Store(var S: TStream);
  begin
    inherited Store( S);
  end;

procedure tMainFunctionDefinition.InitLocalSymbols;
  begin
    LocalSymbols := New(pSymbolTable, Init(stGlobalTable, 0, 4));
    LocalSymbols^.Owner := @Self;
  end;

procedure tMainFunctionDefinition.GenEntryExit( AsmProc: Pointer);
  var
    Size: LongInt;
    I: Integer;
    UI: pUnitItem;
    Str: String;
  begin
    with pProcAsm( AsmProc)^ do
      begin
        if Assigned( UnitCollection) then
          for I := UnitCollection^.Count - 1 downto 0 do
            begin
              UI := UnitCollection^.At( I);
              if Assigned( UI) and Assigned( UI^.SymbolTable) and
                ( UI^.SymbolTable^.HasInit) then
                begin
                  Str := 'U_' + UI^.UnitName^ + '$$init';
                  Insert( New( pAsmInstruction, Create_JSymbol(
                    caiCALL, Str)));
                end;
            end;
        Size := TempSize;
        if Size and 3 <> 0 then Size := Size and not 3 + 4;
        if Size > 0 then
          Insert( New( pAsmInstruction, Create_Reg_Const(
            caiSUB, crESP, Size)));
        Insert( New( pAsmInstruction, Create_Reg_Reg(
          caiMOV, crEBP, crESP)));
        Insert( New( pAsmInstruction, Create_Reg(
          caiPUSH, crEBP)));

        Concat( New( pAsmInstruction, Create_Reg_Reg(
          caiXOR, crEAX, crEAX)));
        Concat( New( pAsmInstruction, Create_JSymbol(
          caiCALL, NameTerminate)));
        {Concat( New( pAsmInstruction, Create_Reg_Const(
          caiMov, crEAX, $4c00)));
        Concat( New( pAsmInstruction, Create_Const(
          caiInt, $21)));}
      end;
  end;




constructor tOrdDefinition.Init( aBaseType: tBaseType; aMin, aMax: LongInt);
  begin
    inherited Init;
    DefType := cOrdDefinition;
    BaseType := aBaseType;
    Min := aMin;
    Max := aMax;
  end;

constructor tOrdDefinition.Load(var S: TStream);
  begin
    inherited Load( S);
    S.Read( BaseType, SizeOf( BaseType));
    S.Read( Min, SizeOf( Min));
    S.Read( Max, SizeOf( Max));
  end;

procedure tOrdDefinition.Store(var S: TStream);
  begin
    inherited Store( S);
    S.Write( BaseType, SizeOf( BaseType));
    S.Write( Min, SizeOf( Min));
    S.Write( Max, SizeOf( Max));
  end;

function tOrdDefinition.GetSize: LongInt;
  begin
    case BaseType of
      cbtByte, cbtShortInt, cbtChar: GetSize := 1;
      cbtWord, cbtInteger: GetSize := 2;
      cbtLongInt, cbtDWord: GetSize := 4;
    end;
  end;


constructor tRealDefinition.Init( aType: tRealType);
  begin
    inherited Init;
    DefType := cRealDefinition;
    RealType := aType;
  end;

constructor tRealDefinition.Load(var S: TStream);
  begin
    inherited Load( S);
    S.Read( RealType, SizeOf( RealType));
  end;

procedure tRealDefinition.Store(var S: TStream);
  begin
    inherited Store( S);
    S.Write( RealType, SizeOf( RealType));
  end;

function tRealDefinition.GetSize: LongInt;
  begin
    case RealType of
      crtSingle: GetSize := 4;
      crtDouble, crtComp: GetSize := 8;
      crtExtended: GetSize := 10;
    end;
  end;


constructor tStringDefinition.Init( aLength: Byte);
  begin
    inherited Init;
    DefType := cStringDefinition;
    Length := aLength;
  end;

constructor tStringDefinition.Load(var S: TStream);
  begin
    inherited Load( S);
    S.Read( Length, SizeOf( Length));
  end;

procedure tStringDefinition.Store(var S: TStream);
  begin
    inherited Store( S);
    S.Write( Length, SizeOf( Length));
  end;

function tStringDefinition.GetSize: LongInt;
  begin
    GetSize := LongInt(Length) + 1;
  end;

function tStringDefinition.GetName: String;
  begin
    if Assigned( Symbol) and (Symbol^._Type = cTypeSymbol) then
      GetName := Symbol^.SymbolName^
    else
      GetName := 'STRING';
  end;


constructor tPointerDefinition.Init( aDef: pDefinition);
  begin
    inherited Init;
    DefType := cPointerDefinition;
    DefinitionType := aDef;
    DefSym := nil;
  end;

constructor tPointerDefinition.Load(var S: TStream);
  var
    DoRead: Boolean;
  begin
    inherited Load( S);
    {S.Read( DoRead, SizeOf( DoRead));}
    DefinitionType := ReadDefinition( S, False);
  end;

procedure tPointerDefinition.Store(var S: TStream);
  var
    DoWrite: Boolean;
  begin
    inherited Store( S);
    {DoWrite := Assigned( DefinitionType) and
      not Assigned( DefinitionType^.Symbol);
    S.Write( DoWrite, SizeOf( DoWrite));}
    WriteDefinition( S, DefinitionType, False);
  end;

function tPointerDefinition.GetSize: LongInt;
  begin
    GetSize := 4;
  end;


constructor tBooleanDefinition.Init( aType: tBoolType);
  begin
    inherited Init;
    DefType := cBooleanDefinition;
    BoolType := aType;
  end;

constructor tBooleanDefinition.Load(var S: TStream);
  begin
    inherited Load( S);
    S.Read( BoolType, SizeOf( BoolType));
  end;

procedure tBooleanDefinition.Store(var S: TStream);
  begin
{writeln( ' boolean store ');}
    inherited Store( S);
    S.Write( BoolType, SizeOf( BoolType));
{writeln( ' boolean ok ');}
  end;

function tBooleanDefinition.GetSize: LongInt;
  begin
    case BoolType of
      cbBoolean: GetSize := 1;
      cbWordBool: GetSize := 2;
      cbLongBool: GetSize := 4;
    end;
  end;


constructor tUserOrdDefinition.Init;
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    DefType := cUserOrdDefinition;
  end;

constructor tUserOrdDefinition.Load(var S: TStream);
  begin
    inherited Load( S);
    S.Read( Max, SizeOf( Max));
  end;

procedure tUserOrdDefinition.Store(var S: TStream);
  begin
    inherited Store( S);
    S.Write( Max, SizeOf( Max));
  end;

function tUserOrdDefinition.GetSize: LongInt;
  begin
    if Max < 256 then
      GetSize := 1
    else if Max < 65536 then
      GetSize := 2
    else
      GetSize := 4;
  end;


constructor tRecordDefinition.Init( aFields: pSymbolTable);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    DefType := cRecordDefinition;
    Fields := aFields;
    if Assigned( Fields) then Fields^.Owner := @Self;
  end;

destructor tRecordDefinition.Done;
  begin
    if Assigned( Fields) then
      Dispose( Fields, Done{$IFDEF PPRO}(){$ENDIF});
    inherited Done{$IFDEF PPRO}(){$ENDIF};
  end;

constructor tRecordDefinition.Load(var S: TStream);
  begin
    inherited Load( S);
    {Fields := pSymbolTable( S.Get);}
    Fields := New( pSymbolTable, Load( S));
    if Assigned( Fields) then
      begin
        Fields^.Owner := @Self;
        Fields^.SymbolTableType := stRecordTable;
      end;
  end;

procedure tRecordDefinition.Store(var S: TStream);
  begin
    inherited Store( S);
    {S.Put( Fields);}
    Fields^.Store( S);
  end;

function tRecordDefinition.GetSize: LongInt;
  begin
    if Assigned( Fields) then
      GetSize := Fields^.DataSize
    else
      GetSize := 0;
  end;

function tRecordDefinition.GetCount: LongInt;
  begin
    GetCount := Fields^.Count;
  end;


constructor tArrayDefinition.Init( aComponent, aIndex: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    DefType := cArrayDefinition;
    ComponentDef := aComponent;
    IndexDef := aIndex;
  end;

destructor tArrayDefinition.Done;
  begin
    {if Assigned( IndexDef) and ( not Assigned( IndexDef^.Symbol) ) then
      Dispose( IndexDef, Done);
    if Assigned( ComponentDef) and ( not Assigned( ComponentDef^.Symbol) ) then
      Dispose( ComponentDef, Done);}
    inherited Done{$IFDEF PPRO}(){$ENDIF};
  end;

constructor tArrayDefinition.Load(var S: TStream);
  begin
    inherited Load( S);
    S.Read( ReadComponent, SizeOf( ReadComponent));
    S.Read( ReadIndex, SizeOf( ReadIndex));
    ComponentDef := ReadDefinition( S, ReadComponent);
    IndexDef := ReadDefinition( S, ReadIndex);
  end;

procedure tArrayDefinition.Store(var S: TStream);
  begin
    inherited Store( S);
    ReadComponent := ComponentDef^.Symbol = nil;
    ReadIndex := IndexDef^.Symbol = nil;
    S.Write( ReadComponent, SizeOf( ReadComponent));
    S.Write( ReadIndex, SizeOf( ReadIndex));
    WriteDefinition( S, ComponentDef, ReadComponent);
    WriteDefinition( S, IndexDef, ReadIndex);
  end;

function tArrayDefinition.GetSize: LongInt;
  var
    ItemCount: LongInt;
  begin
    if IndexDef^.DefType = cOrdDefinition then
      ItemCount := pOrdDefinition( IndexDef)^.Max - pOrdDefinition( IndexDef)^.Min + 1
    else
      ItemCount := pUserOrdDefinition( IndexDef)^.Max + 1;
    GetSize := ItemCount * ComponentDef^.GetSize{$IFDEF PPRO}(){$ENDIF};
  end;

function tArrayDefinition.GetCount: LongInt;
  begin
    if IndexDef^.DefType = cOrdDefinition then
      GetCount := pOrdDefinition( IndexDef)^.Max - pOrdDefinition( IndexDef)^.Min + 1
    else
      GetCount := pUserOrdDefinition( IndexDef)^.Max + 1;
  end;


{ tFileDefinition }
constructor tFileDefinition.Init( aFileType: tFileType; aFileDef: pDefinition);
  begin
    inherited Init{$IFDEF PPRO}(){$ENDIF};
    DefType := cFileDefinition;
    FileType := aFileType;
    FileDef := aFileDef;
  end;

constructor tFileDefinition.Load( var S: tStream);
  begin
    inherited Load( S);
    S.Read( FileType, SizeOf( FileType));
    if FileType = cftTyped then
      begin
        S.Read( ReadFileDef, SizeOf( ReadFileDef) );
        FileDef := ReadDefinition( S, ReadFileDef)
      end
    else
      FileDef := nil;
  end;

procedure tFileDefinition.Store( var S: tStream);
  begin
    inherited Store( S);
    S.Write( FileType, SizeOf( FileType));
    if FileType = cftTyped then
      begin
        ReadFileDef := FileDef^.Symbol = nil;
        S.Write( ReadFileDef, SizeOf( ReadFileDef) );
        WriteDefinition( S, FileDef, ReadFileDef);
      end;
  end;

function tFileDefinition.GetSize: LongInt;
  begin
    case FileType of
      cftTextFile:
         GetSize := 256;
      cftTyped, cftUntyped:
         GetSize := 128;
    end;
  end;


{ tSetDefinition }
constructor tSetDefinition.Init( aSetDef: pDefinition);
  begin
    inherited Init;
    DefType := cSetDefinition;
    SetDef := aSetDef;
    if Assigned( aSetDef) then
      case aSetDef^.DefType of
        cOrdDefinition:
          begin
            Min := pOrdDefinition( aSetDef)^.Min;
            if Min < 0 then
              CurCompiler^.Error( erSetBaseTypeOutOfRange,
                CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol, '');
            Max := pOrdDefinition( aSetDef)^.Max;
          end;
        cUserOrdDefinition:
          Max := pUserOrdDefinition( aSetDef)^.Max;
        cBooleanDefinition:
          Max := 1;
        cAbstractDefinition:;
        else
          CurCompiler^.Error( erOrdinalTypeExpected,
            CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol, '');
      end;
    if Max <= 32 then
      SetType := cstSmallSet
    else if Max <= 256 then
      SetType := cstNormalSet
    else
      CurCompiler^.Error( erSetBaseTypeOutOfRange,
        CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol, '');
  end;

constructor tSetDefinition.Load( var S: tStream);
  begin
    inherited Load( S);
    S.Read( ReadDef, SizeOf( ReadDef));
    S.Read( Min, SizeOf( Min));
    S.Read( Max, SizeOf( Max));
    S.Read( SetType, SizeOf( SetType));
    SetDef := ReadDefinition( S, ReadDef);
  end;

destructor tSetDefinition.Done;
  begin
    {if Assigned( SetDef) and not Assigned( SetDef^.Symbol) then
      Dispose( SetDef, Done);}
    inherited Done{$IFDEF PPRO}(){$ENDIF};
  end;

procedure tSetDefinition.Store( var S: tStream);
  begin
    inherited Store( S);
    ReadDef := SetDef^.Symbol = nil;
    S.Write( ReadDef, SizeOf( ReadDef));
    S.Write( Min, SizeOf( Min));
    S.Write( Max, SizeOf( Max));
    S.Write( SetType, SizeOf( SetType));
    WriteDefinition( S, SetDef, ReadDef);
  end;

function tSetDefinition.GetSize: LongInt;
  begin
    {case SetType of
      cstSmallSet:
        GetSize := 4;
      cstNormalSet:
        GetSize := Range;
      else
        GetSize := 0;
    end;}
    GetSize := (Max + 7) shr 3 - (Min shr 3);
  end;

{ tVMT }
constructor tVMT.Load( var S: tStream);
  var
    aLimit, aDelta, aCount: LongInt;
  begin
    S.Read( aLimit, SizeOf( LongInt));
    S.Read( aDelta, SizeOf( LongInt));
    S.Read( aCount, SizeOf( LongInt));
    inherited Init( aLimit, aDelta);
    for aLimit := 0 to aCount - 1 do
      AtInsert( aLimit, GetItem( S));
  end;

procedure tVMT.Store( var S: tStream);
  var
    L: LongInt;
  begin
    {inherited Store( S);}
    L := Limit;
    S.Write( L, SizeOf( L));
    L := Delta;
    S.Write( L, SizeOf( L));
    L := Count;
    S.Write( L, SizeOf( L));
    for L := 0 to Count - 1 do
      PutItem( S, At( L));
  end;

procedure tVMT.FreeItem( Item: Pointer);
  begin
  end;

function tVMT.GetItem(var S: TStream): Pointer;
  begin
    GetItem := Read_Symbol( S);
  end;

procedure tVMT.PutItem(var S: TStream; Item: Pointer);
  var
    L: LongInt;
  begin
    Write_Symbol( S, Item);
    L := -1;
    S.Write( L, SizeOf( L));
  end;

{ TObjectDefinition }
constructor tObjectDefinition.Init( aBase: pObjectDefinition);

  procedure Copy( Item: Pointer); {$IFDEF TP}far;{$ENDIF}
    begin
      VMTable^.Insert( Item);
    end;

  begin
    inherited Init;
    DefType := cObjectDefinition;
    PublicSymbols := new( pSymbolTable, Init( stObjectTable, 5, 5));
    PublicSymbols^.Owner := @Self;
    Ancestor := aBase;
    VMTable := New( pVMT, Init( 5, 5));
    if Assigned( aBase) then
      aBase^.VMTable^.ForEach( @Copy);
  end;

constructor tObjectDefinition.Load( var S: tStream);
  begin
    inherited Load( S);
    {PublicSymbols := pSymbolTable( S.Get);}
    PublicSymbols := New( pSymbolTable, Load( S));
    if Assigned( PublicSymbols) then
      begin
        PublicSymbols^.Owner := @Self;
        PublicSymbols^.SymbolTableType := stObjectTable;
      end;
    {VMTable := New( pVMT, Init( 5, 5));}
    {VMTable := pVMT( S.Get);}
    VMTable := New( pVMT, Load( S));
    Ancestor := pObjectDefinition( ReadDefinition( S, False));
  end;

destructor tObjectDefinition.Done;
  begin
    if Assigned( PublicSymbols) then
      Dispose( PublicSymbols, Done);
    {if Assigned( PrivateSymbols) then
      Dispose( PrivateSymbols, Done);}
    if Assigned( VMTable) then
      Dispose( VMTable, Done);
    inherited Done;
  end;

procedure tObjectDefinition.Store( var S: tStream);
  begin
    inherited Store( S);
    {S.Put( PublicSymbols);
    S.Put( VMTable);}
    PublicSymbols^.Store( S);
    VMTable^.Store( S);
    WriteDefinition( S, Ancestor, False);
  end;

function tObjectDefinition.GetSize: LongInt;
  var
    Size: LongInt;
  begin
    Size := 0;
    if Assigned( Ancestor) then
      Inc( Size, Ancestor^.GetSize)
    else
      Inc( Size, 4);
    if Assigned( PublicSymbols) then
      Inc( Size, PublicSymbols^.DataSize);
    {if Assigned( PrivateSymbols) then
      Inc( Size, PrivateSymbols^.DataSize);}
    GetSize := Size;
  end;

function tObjectDefinition.MustBeVirtual( Func: pFunctionSymbol): Boolean;

  function Found( Item: pFunctionSymbol): Boolean; {$IFDEF TP}far;{$ENDIF}
    begin
      Found := (Item^._Type = cFunctionSymbol) and
        (Item^.SymbolName^ = Func^.SymbolName^) and
        IsSameParams( Item^.Definition^.ParamColl, Func^.Definition^.ParamColl);
    end;

  var
    Sym: pFunctionSymbol;
  begin
    Sym := VMTable^.FirstThat( @Found);
    MustBeVirtual := Assigned( Sym);
  end;

function tObjectDefinition.MakeVirtual( Func: pFunctionSymbol): Boolean;

  function Found( Item: pFunctionSymbol): Boolean; {$IFDEF TP}far;{$ENDIF}
    begin
{writeln( 'assigned item:', assigned( item));}
      Found := (Item^._Type = cFunctionSymbol) and
        (Item^.SymbolName^ = Func^.SymbolName^) and
        IsSameParams( Item^.Definition^.ParamColl, Func^.Definition^.ParamColl);
    end;

  var
    Sym: pFunctionSymbol;
    I: LongInt;
    Res1, Res2: pDefinition;
  begin
    if Func^.Definition^.ProcOptions and poConstructor <> 0 then
      with CurCompiler^ do
        Error( erVirtualConstructorsAreNotAllowed,
          Files^.PrevLine, Files^.PrevCol, Func^.Name);
    Sym := VMTable^.FirstThat( @Found );
{writeln( 'override method :', assigned( sym));}
    if Assigned( Sym) then
      begin
        Res1 := Sym^.Definition^.ResType;
        Res2 := Func^.Definition^.ResType;
        if ( Assigned( Res1) xor Assigned( Res2)  ) or
          ( Assigned( Res1) and Assigned( Res2) and
          not SameTypes( Res1, Res2) ) then
          with CurCompiler^ do
            Error( erFunctionResultTypeMismatch,
              Files^.PrevLine, Files^.PrevCol, Func^.Name);
        I := VMTable^.IndexOf( Sym);
        {Func^.VirtualIndex := Sym^.VirtualIndex;}
        VMTable^.AtPut( I, Func);
        Inc( I);
      end
    else
      begin
        VMTable^.Insert( Func);
        I := VMTable^.Count;
      end;
    Func^.Definition^.VirtualIndex := I;
    Func^.Definition^.ProcOptions := Func^.Definition^.ProcOptions or
      poVirtualMethod;
  end;

function tObjectDefinition.GetVMTname: String;
  begin
    if Assigned( Symbol) then
      GetVMTname := VMTstr + Symbol^.AsmName{$IFDEF PPRO}(){$ENDIF}
    else
      GetVMTname := '';
  end;

procedure tObjectDefinition.WriteVMT( S: pStream);
  var
    Str: String;

  procedure PutAddress( Item: pFunctionSymbol); {$IFDEF TP}far;{$ENDIF}
    begin
      if not Assigned( Item) then
        Writeln( 'dddddddd');
      Str := ' DD ';
      {if Item^._Type = cFunctionSymbol then}
        Str := Str + _Offset_ + ' ' + Item^.AsmName;
      Str := Str + _EOL_;
      S^.Write( Str[1], Length( Str));
    end;

  begin
    Str := GetVMTname +
      ' DD ' + ToStr( GetSize) + ', -' +
      ToStr( GetSize) + _EOL_;
    S^.Write( Str[1], Length( Str));
    Str := ' DD  0' + _EOL_;
    S^.Write( Str[1], Length( Str));
    VMTable^.ForEach( @PutAddress);
  end;

{ TUnitCollection }
destructor tUnitCollection.Done;
  begin
    while Count > 0 do AtFree( Count - 1);
    inherited Done;
  end;

function tUnitCollection.Compare(Key1, Key2: Pointer): {$IFDEF PPRO}LongInt{$ELSE}Integer{$ENDIF};
  begin
    Compare := 0;
    if Assigned( Key1) and Assigned( Key2) then
      if pString( Key1)^ > pString( Key2)^ then Compare := 1
      else if pString( Key1)^ < pString( Key2)^ then Compare := -1;
  end;

function tUnitCollection.KeyOf(Item: Pointer): Pointer;
  begin
    if Assigned( Item) then
      KeyOf := pUnitItem( Item)^.UnitName
    else
      KeyOf := nil;
  end;

procedure tUnitCollection.Insert( Item: Pointer);
  var
    I: Integer;
  begin
{writeln( pstring( keyof( item))^ );}
{    if not Search( KeyOf( Item), I) then}
      AtInsert( Count, Item);
{inherited Insert( Item);}
  end;

function tUnitCollection.Search(Key: Pointer; var Index: tIndex): Boolean;
  var
    I: tIndex;
    Item: Pointer;
  begin
    for I := 0 to Count - 1 do
      begin
        Item := At(I);
        if (Compare( Key, KeyOf( Item )) = 0){ or
          ( (Item^._Type = cFunctionSymbol) and
          ( Assigned(pFunctionSymbol( Item)^.Alias) ) and
          ( Compare( Key, pFunctionSymbol( Item)^.Alias) = 0 ) )} then
          begin
            Index := I;
            Search := True;
            Exit;
          end;
      end;
    Search := False;
  end;



{procedure DisposeConsts( SymbolTable: pSymbolTable);
  var
    I: LongInt;
  begin
    for I := SymbolTable^.Count - 1 downto 0 do
      if pSymbol( SymbolTable^.At( I))^._Type = cConstSymbol then
        SymbolTable^.AtFree( I);
  end;}

procedure tUnitCollection.FreeItem(Item: Pointer);

  begin
    if Assigned( Item) then with pUnitItem( Item)^ do
      begin
        if Assigned( UnitName) then
          DisposeStr( UnitName);
        if Assigned( SymbolTable) then
          begin
            {DisposeConsts( SymbolTable);}
            Dispose( SymbolTable, Done);
          end;
        Dispose( pUnitItem( Item));
      end;
  end;


procedure RegisterSymbols;
  begin
    RegisterType( RSymbol);
    RegisterType( RSymbolTable);
    RegisterType( RUnitSymbol);
    RegisterType( RFunctionSymbol);
    RegisterType( ROperatorSymbol);
    RegisterType( RTypeSymbol);
    RegisterType( RConstSymbol);
    RegisterType( RVariableSymbol);
    RegisterType( RTypedConstSymbol);
    RegisterType( RUserOrdSymbol);
    RegisterType( RDefinition);
    RegisterType( RFunctionDefinition);
    RegisterType( RFunctionTypeDefinition);
    RegisterType( RMainFunctionDefinition);
    RegisterType( ROrdDefinition);
    RegisterType( RRealDefinition);
    RegisterType( RStringDefinition);
    RegisterType( RPointerDefinition);
    RegisterType( RBooleanDefinition);
    RegisterType( RUserOrdDefinition);
    RegisterType( RArrayDefinition);
    RegisterType( RRecordDefinition);
    RegisterType( RFileDefinition);
    RegisterType( RSetDefinition);
    RegisterType( RObjectDefinition);
    RegisterType( RVMT);
  end;


function IsNumeric( Def: pDefinition): Boolean;
  begin
    if Assigned( Def) then
      IsNumeric := (Def^.DefType = cRealDefinition) or
        ( (Def^.DefType = cOrdDefinition) and
          (pOrdDefinition(Def)^.BaseType <> cbtChar) )
    else
      IsNumeric := False;
  end;


procedure DisposeDefCollection( DefColl: pDefCollection);
  var
    P: pDefCollection;
  begin
    while Assigned( DefColl) do
      begin
        P := DefColl;
        DefColl := DefColl^.Next;
        Dispose(P);
      end;
  end;

procedure WriteDefinition( var S: TStream; Def: pDefinition;DoWrite: Boolean);
  var
    Symbol: pSymbol;
    SymTable: pSymbolTable;
    UnitName: tNameString;
    I: Integer;
    L: LongInt;
  begin
    if Assigned( Def) then
      if DoWrite then
        Def^.Store( S)
        {S.Put( Def)}
      else
        begin
          SymTable := nil;
          UnitName := '';
          Symbol := Def^.Symbol;
          if Assigned( Symbol) then
            SymTable := Symbol^.Owner;
          I := -1;
          if Assigned( SymTable) then
            begin
              I := SymTable^.IndexOf( Symbol);
              UnitName := SymTable^.Name^;
            end;
          S.Write( I, SizeOf(I));
          SymTable := CurCompiler^.UnitSymbol^.UnitSymbols;
          I := -1;
          if Assigned( SymTable) and (UnitName <> '') then
            begin
              Symbol := SymTable^.FindSymbol( UnitName);
              if Assigned( Symbol) then
                I := SymTable^.IndexOf( Symbol);
            end;
          S.Write( I, SizeOf(I));
        end
    else
      begin
        L := -1;
        S.Write( L, SizeOf(L));
      end;
  end;

function ReadDefinition( var S: TStream; DoRead: Boolean): pDefinition;
  var
    L: LongInt;
    SymTable: pSymbolTable;
    Sym: pSymbol;
    DT: tDefinitionType;
  begin
    ReadDefinition := nil;
    if DoRead then
      begin
        S.Read( DT, SizeOf( DT));
        S.Seek( S.GetPos - SizeOf( DT));
        case DT of
          cAbstractDefinition:
            ReadDefinition := New( pDefinition, Load( S));
          cOrdDefinition:
            ReadDefinition := New( pOrdDefinition, Load( S));
          cFunctionDefinition:
            ReadDefinition := New( pFunctionDefinition, Load( S));
          cFunctionTypeDefinition:
            ReadDefinition := New( pFunctionTypeDefinition, Load( S));
          {cMainFunctionDefinition:
            ReadDefinition := New( pMainFunctionDefinition, Load( S));}
          cRealDefinition:
            ReadDefinition := New( pRealDefinition, Load( S));
          cStringDefinition:
            ReadDefinition := New( pStringDefinition, Load( S));
          cPointerDefinition:
            ReadDefinition := New( pPointerDefinition, Load( S));
          cBooleanDefinition:
            ReadDefinition := New( pBooleanDefinition, Load( S));
          cUserOrdDefinition:
            ReadDefinition := New( pUserOrdDefinition, Load( S));
          cRecordDefinition:
            ReadDefinition := New( pRecordDefinition, Load( S));
          cArrayDefinition:
            ReadDefinition := New( pArrayDefinition, Load( S));
          cFileDefinition:
            ReadDefinition := New( pFileDefinition, Load( S));
          cSetDefinition:
            ReadDefinition := New( pSetDefinition, Load( S));
          cObjectDefinition:
            ReadDefinition := New( pObjectDefinition, Load( S));
          else
            with CurCompiler^ do
              Error( erUnitFileFormatError, Files^.PrevLine, Files^.PrevCol, '');
        end;
        {ReadDefinition := pDefinition( S.Get)}
      end
    else
      begin
        S.Read( L, SizeOf( L));
        ReadDefinition := Pointer(L);
      end;
  end;


procedure DecodeSymbol( var Symbol: pSymbol);
  var
    Path: pSymbolPath;
    Sym: pSymbol;
    I: tIndex;
    SymbolTable: pSymbolTable;
    L: LongInt;
  begin
    Path := pSymbolPath( Symbol);
    Sym := nil;
    if Assigned( Path) then
      begin
        if Assigned( UnitCollection) and
          Assigned( Path^.UnitName) and
          UnitCollection^.Search( Path^.UnitName, I) then
          SymbolTable := pUnitItem( UnitCollection^.At( I))^.SymbolTable
        else
          SymbolTable := nil;
        for I := 0 to Path^.PathLength - 1 do
          begin
            L := Path^.Path^[ I];
            if Assigned( SymbolTable) and
              ( L < SymbolTable^.Count ) and ( L >= 0) then
              Sym := SymbolTable^.At( L);
            if not Assigned( Sym) then break;
            SymbolTable := nil;
            case Sym^._Type of
              cUnitSymbol:
                SymbolTable := pUnitSymbol( Sym)^.UnitSymbols;
              cTypeSymbol:
                case (pVariableSymbol( Sym)^.Definition^.DefType) of
                  cRecordDefinition:
                    SymbolTable := pRecordDefinition(
                      pTypeSymbol( Sym)^.Definition)^.Fields;
                  cObjectDefinition:
                    SymbolTable := pObjectDefinition(
                      pTypeSymbol( Sym)^.Definition)^.PublicSymbols;
                end;
              cVariableSymbol,
              cTypedConstSymbol:
                case (pVariableSymbol( Sym)^.Definition^.DefType) of
                  cRecordDefinition:
                    SymbolTable := pRecordDefinition(
                      pVariableSymbol( Sym)^.Definition)^.Fields;
                  cObjectDefinition:
                    SymbolTable := pObjectDefinition(
                      pVariableSymbol( Sym)^.Definition)^.PublicSymbols;
                end;
            end;
          end;
        FreeMem( Path^.Path, Path^.PathLength * SizeOf( LongInt));
        DisposeStr( Path^.UnitName);
        Dispose( Path);
      end;
    Symbol := Sym;
  end;


procedure GetDefinition( var Def: pDefinition; SymTable: pSymbolTable);
  var
    L: LongInt;
    I1, I2: Integer;
    Sym: pSymbol;
    Table: pSymbolTable;
  begin
    L := LongInt( Def);
    I1 := Integer(L and $FFFF);
    I2 := Integer((L and $FFFF0000) shr 16);
    Table := SymTable;
    if Assigned( SymTable) and (I2 >= 0) and (I2 < SymTable^.Count) then
      begin
        Sym := SymTable^.At( I2);
        if Sym^._Type = cUnitSymbol then
          Table := pUnitSymbol( Sym)^.UnitSymbols;
      end;
    Sym := nil;
    if Assigned( Table) and (I1 >= 0) and (I1 < Table^.Count) then
      Sym := Table^.At( I1);
    Def := nil;
    if Assigned( Sym) then
      case Sym^._Type of
        cTypeSymbol:
          Def := pTypeSymbol( Sym)^.Definition;
        cVariableSymbol,
        cTypedConstSymbol:
          Def := pVariableSymbol( Sym)^.Definition;
      end;
  end;

procedure MakeDefinition( var Def: pDefinition; SymTable: pSymbolTable);
  var
    DefColl: pDefCollection;
    I: Integer;
    Sym: pSymbol;
  begin
    if Assigned( Def) then
      case Def^.DefType of
        cPointerDefinition:
          with pPointerDefinition( Def)^ do
            begin
              GetDefinition( DefinitionType, SymTable);
            end;
        cSetDefinition:
          with pSetDefinition( Def)^ do
            begin
              if ReadDef then
                MakeDefinition( SetDef, SymTable)
              else
                GetDefinition( SetDef, SymTable);
            end;
        cArrayDefinition:
          with pArrayDefinition( Def)^ do
            begin
              if ReadComponent then
                MakeDefinition( ComponentDef, SymTable)
              else
                GetDefinition( ComponentDef, SymTable);
              if ReadIndex then
                MakeDefinition( IndexDef, SymTable)
              else
                GetDefinition( IndexDef, SymTable);
            end;
        cFunctionDefinition:
          with pFunctionDefinition( Def)^ do
            begin
              DefColl := ParamColl;
              while Assigned( DefColl) do
                begin
                  GetDefinition( DefColl^.Definition, SymTable);
                  DefColl := DefColl^.Next;
                end;
              GetDefinition( ResType, SymTable);
              GetDefinition( pDefinition( ObjectDef), SymTable);
            end;
        cFunctionTypeDefinition:
          with pAbstractFunctionDefinition( Def)^ do
            begin
              DefColl := ParamColl;
              while Assigned( DefColl) do
                begin
                  GetDefinition( DefColl^.Definition, SymTable);
                  DefColl := DefColl^.Next;
                end;
              GetDefinition( ResType, SymTable);
            end;
        cRecordDefinition:
          with pRecordDefinition( Def)^ do
            if Assigned( Fields) then
              begin
                for I := 0 to Fields^.Count - 1 do
                  ResolveDefinitions( Fields^.At( I), SymTable);
              end;
        cFileDefinition:
          with pFileDefinition( Def)^ do
            begin
              if ReadFileDef then
                MakeDefinition( FileDef, SymTable)
              else
                GetDefinition( FileDef, SymTable);
            end;
        cObjectDefinition:
          with pObjectDefinition( Def)^ do
            begin
              if Assigned( PublicSymbols) then
                begin
                  for I := 0 to PublicSymbols^.Count - 1 do
                    ResolveDefinitions( PublicSymbols^.At( I), SymTable);
                end;
              if Assigned( VMTable) then
                for I := 0 to VMTable^.Count - 1 do
                  begin
                    Sym := VMTable^.At( I);
                    DecodeSymbol( Sym);
                    VMTable^.AtPut( I, Sym);
                  end;
              GetDefinition( pDefinition( Ancestor), SymTable);
            end;
      end;
  end;


procedure ResolveDefinitions( Symbol: pSymbol; SymTable: pSymbolTable);
  begin
    case Symbol^._Type of
      cTypeSymbol:
        if not pTypeSymbol( Symbol)^.IsOwner then
          GetDefinition( pTypeSymbol( Symbol)^.Definition, SymTable)
        else
          MakeDefinition( pTypeSymbol( Symbol)^.Definition, SymTable);
      cTypedConstSymbol,
      cVariableSymbol:
        if not pVariableSymbol( Symbol)^.IsOwner then
          GetDefinition( pVariableSymbol( Symbol)^.Definition, SymTable)
        else
          MakeDefinition( pVariableSymbol( Symbol)^.Definition, SymTable);
      cAbsoluteSymbol:
        begin
          if not pAbsoluteSymbol( Symbol)^.IsOwner then
            GetDefinition( pAbsoluteSymbol( Symbol)^.Definition, SymTable)
          else
            MakeDefinition( pAbsoluteSymbol( Symbol)^.Definition, SymTable);
          if pAbsoluteSymbol( Symbol)^.AbsoluteType = catVariable then
            DecodeSymbol( pSymbol( pAbsoluteSymbol( Symbol)^.Reference) );
        end;
      cConstSymbol:
        begin
          GetDefinition( pConstSymbol( Symbol)^.ConstType, SymTable);
          {if pConstSymbol( Symbol)^.ConstType^.DefType = cPointerDefinition then
            DecodeSymbol( pPointerValue(pConstSymbol( Symbol)^.Value.InfoPtr)^.Symbol );}
        end;
      cFunctionSymbol,
      cOperatorSymbol:
        begin
          MakeDefinition( pDefinition(pFunctionSymbol( Symbol)^.Definition), SymTable);
          if Assigned( pFunctionSymbol( Symbol)^.NextOverloaded) then
            begin
              DecodeSymbol( pSymbol( pFunctionSymbol( Symbol)^.NextOverloaded) );
              {pFunctionSymbol( Symbol)^.NextOverloaded^.Owner := Symbol^.Owner;
              ResolveDefinitions( pFunctionSymbol( Symbol)^.NextOverloaded, SymTable);}
            end;
        end;
      cUserOrdSymbol:
        GetDefinition( pDefinition(pUserOrdSymbol( Symbol)^.Definition), SymTable);
    end;
  end;


procedure InitUnitCollection;
  begin
    UnitCollection := New( pUnitCollection, Init( 5, 5));
  end;

procedure DoneUnitCollection;
  begin
    if Assigned( UnitCollection) then
      Dispose( UnitCollection, Done);
    UnitCollection := nil;
  end;


function CreateUnitItem( const UnitName: String; SymbolTable: pSymbolTable;
    UsedUnits: pFileCollection; LinkFiles: pFileCollection):
  pUnitItem;
  var
    UI: pUnitItem;
  begin
    New( UI);
    UI^.UnitName := NewStr( UnitName);
    UI^.SymbolTable := SymbolTable;
    UI^.IsUnitCompiled := False;
    UI^.IsInterfaceReady := True;
    UI^.Compiler := nil;
    UI^.UsedUnits := UsedUnits;
    UI^.LinkFiles := LinkFiles;
    CreateUnitItem := UI;
  end;


function ReadSymbol( var S: tStream): pSymbol;
  var
    SymType: tSymbolType;
  begin
    S.Read( SymType, SizeOf( SymType));
    ReadSymbol := nil;
    case SymType of
      cFunctionSymbol:
        ReadSymbol := New( pFunctionSymbol, Load( S));
      cOperatorSymbol:
        ReadSymbol := New( pOperatorSymbol, Load( S));
      cTypeSymbol:
        ReadSymbol := New( pTypeSymbol, Load( S));
      cConstSymbol:
        ReadSymbol := New( pConstSymbol, Load( S));
      cVariableSymbol:
        ReadSymbol := New( pVariableSymbol, Load( S));
      cTypedConstSymbol:
        ReadSymbol := New( pTypedConstSymbol, Load( S));
      cAbsoluteSymbol:
        ReadSymbol := New( pAbsoluteSymbol, Load( S));
      cUserOrdSymbol:
        ReadSymbol := New( pUserOrdSymbol, Load( S));
      cUnitSymbol:
        ReadSymbol := New( pUnitSymbol, Load( S));
      cSystemSymbol:
        ReadSymbol := New( pSystemSymbol, Load( S));
      else
        CurCompiler^.Error( erUnitFileFormatError,
          CurCompiler^.Files^.PrevLine, CurCompiler^.Files^.PrevCol, '');
    end;
  end;

procedure ReadConstValue( var S: tStream; var Value: tValue);
  var
    {I: Integer;}
    L, L1: LongInt;
    CodeType: tCodeType;
  begin
    S.Read( Value.ValueType, SizeOf( Value.ValueType));
    case Value.ValueType of
      cvOrdinalValue:
        S.Read( Value.IntValue, SizeOf( Value.IntValue));
      cvRealValue:
        S.Read( Value.RealValue, SizeOf( Value.RealValue));
      cvStringValue:
        Value.StringValue := S.ReadStr{$IFDEF PPRO}(){$ENDIF};
      cvRecordValue,
      cvArrayValue:
        begin
          S.Read( L, SizeOf( L));
          GetMem( Value.InfoPtr, L * SizeOf( tValue) );
          for L1 := 0 to L - 1 do
            ReadConstValue( S, pValueArray( Value.InfoPtr)^[ L]);
        end;
      cvAddressValue:
        begin
          GetMem( Value.InfoPtr, SizeOf( tPointerValue));
          S.Read( pPointerValue( Value.InfoPtr)^.Offset, SizeOf( LongInt));
          pPointerValue( Value.InfoPtr)^.AsmLabel := S.ReadStr;
        end;
    end;
  end;

procedure WriteConstValue( var S: tStream; Value: tValue;
  ConstType: pDefinition);
  var
    I: Integer;
    L: LongInt;
    UnitName: tNameString;
    SymTable: pSymbolTable;
    Sym: pSymbol;
    Str: String;
  begin
    case Value.ValueType of
      cvOrdinalValue:
        begin
          S.Write( Value, SizeOf( Value.ValueType) + SizeOf( Value.IntValue));
        end;
      cvRealValue:
        begin
          S.Write( Value, SizeOf( Value.ValueType) + SizeOf( Value.RealValue));
        end;
      cvStringValue:
        begin
          S.Write( Value.ValueType, SizeOf( Value.ValueType));
          S.WriteStr( Value.StringValue);
        end;
      cvRecordValue:
        begin
          L := pRecordDefinition( ConstType)^.GetCount{$IFDEF PPRO}(){$ENDIF};
          S.Write( L, SizeOf( L));
          for I := 0 to L - 1 do
            WriteConstValue( S, pValueArray( @Value)^[ I],
              pRecordDefinition( ConstType)^.Fields^.At( I));
        end;
      cvArrayValue:
        begin
          L := pArrayDefinition( ConstType)^.GetCount{$IFDEF PPRO}(){$ENDIF};
          S.Write( L, SizeOf( L));
          for I := 0 to L - 1 do
            WriteConstValue( S, pValueArray( @Value)^[ I],
              pArrayDefinition( ConstType)^.ComponentDef);
        end;
      cvAddressValue:
        begin
          S.Write( Value.ValueType, SizeOf( Value.ValueType));
          S.Write( pPointerValue( Value.InfoPtr)^.Offset, SizeOf( LongInt));
          if Assigned( pPointerValue( Value.InfoPtr)^.AsmLabel) then
            Str := pPointerValue( Value.InfoPtr)^.AsmLabel^
          else if Assigned(  pPointerValue( Value.InfoPtr)^.Symbol) then
            Str := pPointerValue( Value.InfoPtr)^.Symbol^.AsmName
          else
            Str := '';
          S.WriteStr( @Str)
        end;
    end;
  end;


function SameTypes( Def1, Def2: pDefinition): Boolean;
  begin
    case Def1^.DefType of
      cStringDefinition:
        SameTypes := Def2^.DefType = cStringDefinition;
      cOrdDefinition:
        SameTypes := (Def2^.DefType = cOrdDefinition) and
          (pOrdDefinition( Def1)^.BaseType = pOrdDefinition( Def2)^.BaseType);
      cAbstractDefinition:
        SameTypes := True;
      cRealDefinition:
        SameTypes :=
          pRealDefinition( Def1)^.RealType = pRealDefinition( Def2)^.RealType;
      cPointerDefinition:
        SameTypes := (Def2^.DefType = cPointerDefinition) and
          {(pPointerDefinition( Def1)^.DefinitionType^.DefType =
          pPointerDefinition( Def2)^.DefinitionType^.DefType) and}
          SameTypes( pPointerDefinition( Def1)^.DefinitionType,
            pPointerDefinition( Def2)^.DefinitionType );
      cObjectDefinition:
        SameTypes := (Def1 = Def2) or
          {(Def2^.DefType = cAbstractDefinition) or}
          IsAncestor( pObjectDefinition( Def1),
            pObjectDefinition( Def2) );
      cSetDefinition:
        if Def2^.DefType = cSetDefinition then
          SameTypes := pSetDefinition( Def1)^.SetDef =
            pSetDefinition( Def2)^.SetDef
        else
          SameTypes := False;
      cFileDefinition:
        if pFileDefinition( Def1)^.FileType <>
          pFileDefinition( Def2)^.FileType then
          SameTypes := False
        else
          case pFileDefinition( Def1)^.FileType of
            cftTextFile,
            cftUntyped:
              SameTypes := True;
            cftTyped:
              SameTypes := CompatibleTypes(
                pFileDefinition( Def1)^.FileDef,
                pFileDefinition( Def2)^.FileDef);
          end;
      else
        SameTypes := (Def1 = Def2) {or (Def2^.DefType = cAbstractDefinition)};
    end;
  end;

function EqualTypes( Def1, Def2: pDefinition): Boolean;
  begin
    EqualTypes := False;
    if Assigned( Def1) and Assigned( Def2) then
      begin
        if (Def1^.DefType = cAbstractDefinition) or
           (Def2^.DefType = cAbstractDefinition) then
             EqualTypes := True
        else if Def1^.DefType = Def2^.DefType then
          case Def1^.DefType of
            cOrdDefinition:
              case pOrdDefinition( Def1)^.BaseType of
                cbtChar:
                  EqualTypes :=  pOrdDefinition( Def2)^.BaseType = cbtChar;
                cbtByte, cbtWord, cbtDWord:
                  EqualTypes :=  pOrdDefinition( Def2)^.BaseType in
                    [cbtByte, cbtWord, cbtDWord];
                else
                  EqualTypes :=  pOrdDefinition( Def2)^.BaseType in
                    [cbtShortInt, cbtInteger, cbtLongInt];
              end;
            cPointerDefinition:
               EqualTypes := CompatibleTypes(
                 pPointerDefinition( Def1)^.DefinitionType,
                 pPointerDefinition( Def2)^.DefinitionType );
            cStringDefinition:
              EqualTypes := pStringDefinition( Def1)^.Length =
                pStringDefinition( Def2)^.Length;
            cObjectDefinition:
              EqualTypes := (Def1 = Def2) or
                (Def2^.DefType = cAbstractDefinition) or
                IsAncestor( pObjectDefinition( Def1),
                  pObjectDefinition( Def2) );
              {EqualTypes := (Def1 = Def2) or
                IsAncestor( pObjectDefinition( Def1),
                  pObjectDefinition( Def2) );}
            cFileDefinition:
              if pFileDefinition( Def1)^.FileType <>
                pFileDefinition( Def2)^.FileType then
                EqualTypes := False
              else
                case pFileDefinition( Def1)^.FileType of
                  cftTextFile,
                  cftUntyped:
                    EqualTypes := True;
                  cftTyped:
                    EqualTypes := EqualTypes(
                      pFileDefinition( Def1)^.FileDef,
                      pFileDefinition( Def2)^.FileDef);
                end;
             cSetDefinition:
               EqualTypes := EqualTypes(
                 pSetDefinition( Def1)^.SetDef,
                 pSetDefinition( Def2)^.SetDef);
             else
               EqualTypes := Def1 = Def2;
           end;
      end;
  end;

function IsSameParams( Def1, Def2: pDefCollection): Boolean;
  begin
    while Assigned( Def1) and Assigned( Def2) do
      begin
        case Def1^.ParamType of
          cvtStringParam,
          cvtConstParam,
          cvtParam:
            if (Def2^.ParamType in [cvtParam, cvtVarParam, cvtStringParam, cvtConstParam]) then
              begin
                if not SameTypes( Def1^.Definition, Def2^.Definition) then
                  begin
                    IsSameParams := False;
                    Exit;
                  end;
              end;
          cvtVarParam:
            if (Def2^.ParamType = cvtVarParam) then
              begin
                if not SameTypes( Def1^.Definition, Def2^.Definition) then
                  begin
                    IsSameParams := False;
                    Exit;
                  end;
              end;
          else
            begin
              IsSameParams := False;
              Exit;
            end;
        end;
        Def1 := Def1^.Next;
        Def2 := Def2^.Next;
      end;
    IsSameParams := not Assigned( Def1) and not Assigned( Def2);
  end;

function IsEqualParams( Def1, Def2: pDefCollection): Boolean;
  begin
    while Assigned( Def1) and Assigned( Def2) do
      begin
        case Def1^.ParamType of
          cvtStringParam,
          cvtConstParam,
          cvtParam:
            if (Def2^.ParamType in [cvtParam, cvtVarParam, cvtConstParam, cvtStringParam]) then
              begin
                if not EqualTypes( Def1^.Definition, Def2^.Definition) then
                  begin
                    IsEqualParams := False;
                    Exit;
                  end;
              end;
          cvtVarParam:
            if (Def2^.ParamType = cvtVarParam) then
              begin
                if not SameTypes( Def1^.Definition, Def2^.Definition) then
                  begin
                    IsEqualParams := False;
                    Exit;
                  end;
              end;
          else
            begin
              IsEqualParams := False;
              Exit;
            end;
        end;
        Def1 := Def1^.Next;
        Def2 := Def2^.Next;
      end;
    IsEqualParams := not Assigned( Def1) and not Assigned( Def2);
  end;

function CompatibleTypes( Def1, Def2: pDefinition): Boolean;
  begin
    CompatibleTypes := False;
    if Assigned( Def1) and Assigned( Def2) then
      if Def1^.DefType = Def2^.DefType then
        case Def1^.DefType of
          cAbstractDefinition:
            CompatibleTypes := True;
          cStringDefinition:
            CompatibleTypes := True;
          cRealDefinition:
            CompatibleTypes := True;
          cOrdDefinition:
            if pOrdDefinition( Def1)^.BaseType <> cbtChar then
              CompatibleTypes :=  pOrdDefinition( Def2)^.BaseType <> cbtChar
            else
              CompatibleTypes :=  pOrdDefinition( Def2)^.BaseType = cbtChar;
          cPointerDefinition:
            CompatibleTypes := CompatibleTypes(
              pPointerDefinition( Def1)^.DefinitionType,
              pPointerDefinition( Def2)^.DefinitionType );
          {cFunctionTypeDefinition:
            CompatibleTypes := }
          cObjectDefinition:
            CompatibleTypes := (Def1 = Def2) or
              IsAncestor( pObjectDefinition( Def1),
                pObjectDefinition( Def2));
          cFileDefinition:
            if pFileDefinition( Def1)^.FileType <>
              pFileDefinition( Def2)^.FileType then
              CompatibleTypes := False
            else
              case pFileDefinition( Def1)^.FileType of
                cftTextFile,
                cftUntyped:
                  CompatibleTypes := True;
                cftTyped:
                  CompatibleTypes := CompatibleTypes(
                    pFileDefinition( Def1)^.FileDef,
                    pFileDefinition( Def2)^.FileDef);
              end;
          cSetDefinition:
            CompatibleTypes := CompatibleTypes(
              pSetDefinition( Def1)^.SetDef,
              pSetDefinition( Def2)^.SetDef);
          else
            if Def2^.DefType <> cAbstractDefinition then
              CompatibleTypes := Def1 = Def2
            else
              CompatibleTypes := True;
        end
      else if (Def1^.DefType = cAbstractDefinition) or
        (Def2^.DefType = cAbstractDefinition) then
          CompatibleTypes := True
      else if (Def1^.DefType = cStringDefinition) and
        ( (Def2^.DefType = cOrdDefinition) and
        (pOrdDefinition( Def2)^.BaseType = cbtChar) ) then
          CompatibleTypes := True
      else if ( Def1^.DefType = cRealDefinition) and IsNumeric( Def2) then
        CompatibleTypes := True
      {else if (Def1^.DefType = cFunctionTypeDefinition) and
        (Def2^.DefType = cPointerDefinition) and
        (pPointerDefinition( Def2)^.DefinitionType^.DefType = cAbstractDefinition) then
        CompatibleTypes := True};
  end;

function IsCompatible( Def1, Def2: pDefCollection): Boolean;
  begin
    while Assigned( Def1) and Assigned( Def2) do
      begin
        case Def1^.ParamType of
          cvtStringParam,
          cvtConstParam,
          cvtParam:
            if (Def2^.ParamType in [cvtParam, cvtVarParam, cvtConstParam, cvtStringParam]) then
              begin
                if not CompatibleTypes( Def1^.Definition, Def2^.Definition) then
                  begin
                    IsCompatible := False;
                    Exit;
                  end;
              end;
          cvtVarParam:
            if (Def2^.ParamType = cvtVarParam) then
              begin
                if not SameTypes( Def1^.Definition, Def2^.Definition) then
                  begin
                    IsCompatible := False;
                    Exit;
                  end;
              end;
          else
            begin
              IsCompatible := False;
              Exit;
            end;
        end;
        Def1 := Def1^.Next;
        Def2 := Def2^.Next;
      end;
    IsCompatible := not Assigned( Def1) and not Assigned( Def2);
  end;


function IsOldUnit( const FileName: PathStr): Boolean;
  var
    S: pBufStream;
    StrColl: pFileDateCollection;
    IsOld: Boolean;

  procedure CheckUnit( UnitName: pString); {$IFDEF TP}far;{$ENDIF}
    begin
    end;

  begin
    S := New( pBufStream, Init( FileName, stOpenRead, 1024));
    IsOld := True;
    if S^.Status = stOk then
      begin
        IsOld := False;
        {StrColl := pFileDateCollection( S^.Get);
        if (S^.Status = stOK) and Assigned( StrColl) and
          (TypeOf( StrColl^) = TypeOf( tStringCollection)) then
            StrColl^.ForEach( @CheckUnit);
        if not IsOld then;}
      end;
    Dispose( S, Done{$IFDEF PPRO}(){$ENDIF});
    IsOldUnit := IsOld;
  end;


function NewPointerValue( Symbol: pSymbol; AsmLabel: pString; Offset: LongInt): pPointerValue;
  var
   P: pPointerValue;
  begin
    New( P);
    P^.Symbol := Symbol;
    P^.Offset := Offset;
    P^.AsmLabel := AsmLabel;
    NewPointerValue := P;
  end;


procedure Write_Symbol( var S: tStream; Symbol: pSymbol);
  var
    L: LongInt;
    SymbolTable: pSymbolTable;
  begin
    if Assigned( Symbol) and Assigned( Symbol^.Owner) then
      begin
        SymbolTable :=  Symbol^.Owner;
        case SymbolTable^.SymbolTableType of
          stUnitTable:
            begin
              S.WriteStr( SymbolTable^.Name);
              {Exit;}
            end;
          stObjectTable,
          stRecordTable:
            begin
              Write_Symbol( S, pDefinition( SymbolTable^.Owner)^.Symbol);
            end;
        end;
        L := SymbolTable^.IndexOf( Symbol);
        S.Write( L, SizeOf( LongInt));
      end;
  end;

function Read_Symbol( var S: tStream): pSymbolPath;
  var
    Path: pSymbolPath;
    P: pLongIntArray;
    L: LongInt;
  begin
    New( Path);
    Path^.PathLength := 0;
    Path^.Path := nil;
    Path^.UnitName := S.ReadStr;
    S.Read( L, SizeOf( LongInt));
    while L >= 0 do
      begin
        GetMem( P, (Path^.PathLength + 1) * SizeOf( LongInt));
        if Assigned( Path^.Path) then
          begin
            Move( Path^.Path^, P^, Path^.PathLength * SizeOf( LongInt));
            FreeMem( Path^.Path, Path^.PathLength * SizeOf( LongInt));
          end;
        Path^.Path := P;
        Path^.Path^[ Path^.PathLength] := L;
        Inc( Path^.PathLength);
        S.Read( L, SizeOf( LongInt));
      end;
    Read_Symbol := Path;
  end;


procedure DisposeDefinitions;
  var
    P: pDefinition;
  begin
    while Assigned( DefinitionList) do
      begin
        P := DefinitionList;
        DefinitionList := P^.NextDefinition;
        Dispose( P, Done);
      end;
  end;


end.