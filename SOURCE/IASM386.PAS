{                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/gpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

{
  Дата создания: 28.09.97
  В этом модуле содержится набор средтсв для управления нузкоуровненвым
  ассемблерным кодом.

  + 12.02.98 added Prefix and LabelName to tAsmInstruction
  - 12.02.98 removed tAbstractAsmInstruction and tLabeledInstruction
}

{$IFDEF TP}
{$X+,V-,G+,N+,E-,B-,T-}
{$IFDEF DEBUG}
{$I+,S+,R+,C+}
{$ELSE}
{$I-,S-,R-,C-}
{$ENDIF}
{$ENDIF}

unit IAsm386;

interface

uses Objects;

{const
  otNone        = 0;
  otRegister    = 1;
  otConst       = 2;
  otReference   = 3;
  otSymbol      = 4;}

type
  tAsmOp =(caiNoInstruction, caiMOV,caiMOVZX,caiMOVSX,caiLABEL,caiADD,
    caiCALL,caiIDIV,caiIMUL,caiJMP,caiLEA,caiMUL,caiNEG,caiNOT,
    caiPOP,caiPOPAD,caiPUSH,caiPUSHAD,caiRET, caiRETF,caiSUB,caiXCHG,caiXOR,
    caiFILD,caiCMP,caiJZ,caiINC,caiDEC,caiSETE,caiSETNE,caiSETL,
    caiSETG,caiSETLE,caiSETGE,caiJE,caiJNE,caiJL,caiJG,caiJLE,caiJGE,
    caiOR,caiFLD,caiFADD,caiFMUL,caiFSUB,caiFDIV,caiFCHS,caiFLD1,
    caiFIDIV,caiCLTD,caiJNZ,caiFSTP,caiAND,caiJNO,caiNOTH,caiNONE,
    caiENTER,caiLEAVE,caiCLD,caiMOVS,caiREP,caiSHL,caiSHR,caiBOUND,
    caiJNS,caiJS,caiJO,caiSAR,caiTEST,
    caiFCOM,caiFCOMP,caiFCOMPP,caiFXCH,caiFADDP,caiFMULP,caiFSUBP,caiFDIVP,
    caiFNSTS,caiSAHF,caiFDIVRP,caiFSUBRP,caiSETC,caiSETNC,caiJC,caiJNC,
    caiJA,caiJAE,caiJB,caiJBE,caiSETA,caiSETAE,caiSETB,caiSETBE,
    caiAAA,caiAAD,caiAAM,caiAAS,caiCBW,caiCDQ,caiCLC,caiCLI,
    caiCLTS,caiCMC,caiCWD,caiCWDE,caiDAA,caiDAS,caiHLT,caiIRET,caiLAHF,
    caiLODS,caiLODSB,caiLODSW,caiLODSD,caiLOCK,caiNOP,caiPUSHA,
    caiPUSHF, caiPUSHFW, caiPUSHFD,
    caiSTC,caiSTD,caiSTI,caiSTOS,caiSTOSB,caiSTOSW,caiSTOSD,caiWAIT,
    caiXLAT,caiXLATB,caiMOVSB,
    caiMOVSW,caiMOVSD,caiMOVZB,caiMOVZWL,caiPOPA,caiIN,
    caiOUT,caiLDS,caiLCS,caiLES,caiLFS,caiLGS,caiLSS,caiPOPF,caiSBB,caiADC,
    caiDIV,caiROR,caiROL,caiRCL,caiRCR,caiSAL,caiSHLD,caiSHRD,
    caiLCALL,caiLJMP,caiLRET,caiJNAE,caiJNB,caiJNA,caiJNBE,caiJP,caiJNP,
    caiJPE,caiJPO,caiJNGE,caiJNG,caiJNL,caiJNLE,caiJCXZ,caiJECXZ,

    caiLOOP,caiCMPS,caiCMPSB,caiCMPSW,caiCMPSD,caiINS,caiINSB,caiINSW,caiINSD,
    caiOUTS,caiOUTSB,caiOUTSW,caiOUTSD,caiSCAS,caiSCASB,caiSCASW,caiSCASD,
    caiBSF,caiBSR,caiBT,caiBTC,caiBTR,caiBTS,caiINT,caiINT3,caiINTO,caiBOUNDL,caiBOUNDW,
    caiLOOPZ,caiLOOPE,caiLOOPNZ,caiLOOPNE,caiSETO,caiSETNO,caiSETNAE,caiSETNB,
    caiSETZ,caiSETNZ,caiSETNA,caiSETNBE,caiSETS,caiSETNS,caiSETP,caiSETPE,caiSETNP,
    caiSETPO,caiSETNGE,caiSETNL,caiSETNG,caiSETNLE,caiARPL,caiLAR,caiLGDT,caiLIDT,
    caiLLDT,caiLMSW,caiLSL,caiLTR,caiSGDT,caiSIDT,caiSLDT,caiSMSW,caiSTR,caiVERR,caiVERW,

    caiFABS,caiFBLD,caiFBSTP,caiFCLEX,caiFNCLEX,
    caiFCOS,caiFDECSTP,caiFDISI,caiFNDISI,
    caiFDIVR,caiFENI,caiFNENI,caiFFREE,caiFIADD,caiFICOM,caiFICOMP,
    caiFIDIVR,caiFIMUL,caiFINCSTP,caiFINIT,caiFNINIT,caiFIST,caiFISTP,caiFISUB,
    caiFISUBR,caiFLDCW,caiFLDENV,caiFLDLG2,caiFLDLN2,caiFLDL2E,
    caiFLDL2T,caiFLDPI,caiFLDS,caiFLDZ,caiFNOP,caiFPATAN,
    caiFPREM,caiFPREM1,caiFPTAN,caiFRNDINT,caiFRSTOR,caiFSAVE,caiFNSAVE,
    caiFSCALE,caiFSETPM,caiFSIN,caiFSINCOS,caiFSQRT,caiFST,caiFSTCW,caiFNSTCW,
    caiFSTENV,caiFNSTENV,caiFSTSW,caiFNSTSW,caiFTST,caiFUCOM,caiFUCOMP,
    caiFUCOMPP,caiFWAIT,caiFXAM,caiFXTRACT,caiFYL2X,caiFYL2XP1,caiF2XM1,
    caiFILDQ,caiFILDS,caiFILDL,caiFLDL,caiFLDT,caiFISTQ,caiFISTS,caiFISTL,caiFSTL,caiFSTS,
    caiFSTPS,caiFISTPL,caiFSTPL,caiFISTPS,caiFISTPQ,caiFSTPT,
    caiFCOMPS,caiFICOMPL,caiFCOMPL,caiFICOMPS,
    caiFCOMS,caiFICOML,caiFCOML,caiFICOMS,caiFIADDL,caiFADDL,caiFIADDS,
    caiFISUBL,caiFSUBL,caiFISUBS,caiFSUBS,caiFSUBR,caiFSUBRS,caiFISUBRL,
    caiFSUBRL,caiFISUBRS,caiFMULS,caiFIMULL,caiFMULL,caiFIMULS,caiFDIVS,caiFIDIVL,
    caiFDIVL,caiFIDIVS,caiFDIVRS,caiFIDIVRL,caiFDIVRL,caiFIDIVRS,
    caiREPE,caiREPNE,caiFADDS
  );

const
  OpName: array [ tAsmOp] of String[7] =
  ( '', 'MOV', 'MOVZX', 'MOVSX', 'LABEL', 'ADD',
    'CALL', 'IDIV', 'IMUL', 'JMP', 'LEA', 'MUL', 'NEG', 'NOT',
    'POP', 'POPAD', 'PUSH', 'PUSHAD', 'RET', 'RETF', 'SUB', 'XCHG', 'XOR',
    'FILD', 'CMP', 'JZ', 'INC', 'DEC', 'SETE', 'SETNE', 'SETL',
    'SETG', 'SETLE', 'SETGE', 'JE', 'JNE', 'JL', 'JG', 'JLE', 'JGE',
    'OR', 'FLD', 'FADD', 'FMUL', 'FSUB', 'FDIV', 'FCHS', 'FLD1',
    'FIDIV', 'CLTD', 'JNZ', 'FSTP', 'AND', 'JNO', 'NOTH', 'NONE',
    'ENTER', 'LEAVE', 'CLD', 'MOVS', 'REP', 'SHL', 'SHR', 'BOUND',
    'JNS', 'JS', 'JO', 'SAR', 'TEST',
    'FCOM', 'FCOMP', 'FCOMPP', 'FXCH', 'FADDP', 'FMULP', 'FSUBP', 'FDIVP',
    'FNSTS', 'SAHF', 'FDIVRP', 'FSUBRP', 'SETC', 'SETNC', 'JC', 'JNC',
    'JA', 'JAE', 'JB', 'JBE', 'SETA', 'SETAE', 'SETB', 'SETBE',
    'AAA', 'AAD', 'AAM', 'AAS', 'CBW', 'CDQ', 'CLC', 'CLI',
    'CLTS', 'CMC', 'CWD', 'CWDE', 'DAA', 'DAS', 'HLT', 'IRET', 'LAHF',
    'LODS', 'LODSB', 'LODSW', 'LODSD', 'LOCK', 'NOP', 'PUSHA',
    'PUSHF', 'PUSHFW', 'PUSHFD',
    'STC', 'STD', 'STI', 'STOS', 'STOSB', 'STOSW', 'STOSD', 'WAIT',
    'XLAT', 'XLATB', 'MOVSB',
    'MOVSW', 'MOVSD', 'MOVZB', 'MOVZWL', 'POPA', 'IN',
    'OUT', 'LDS', 'LCS', 'LES', 'LFS', 'LGS', 'LSS', 'POPF', 'SBB', 'ADC',
    'DIV', 'ROR', 'ROL', 'RCL', 'RCR', 'SAL', 'SHLD', 'SHRD',
    'LCALL', 'LJMP', 'LRET', 'JNAE', 'JNB', 'JNA', 'JNBE', 'JP', 'JNP',
    'JPE', 'JPO', 'JNGE', 'JNG', 'JNL', 'JNLE', 'JCXZ', 'JECXZ',

    'LOOP', 'CMPS', 'CMPSB', 'CMPSW', 'CMPSD', 'INS', 'INSB', 'INSW', 'INSD',
    'OUTS', 'OUTSB', 'OUTSW', 'OUTSD', 'SCAS', 'SCASB', 'SCASW', 'SCASD',
    'BSF', 'BSR', 'BT', 'BTC', 'BTR', 'BTS', 'INT', 'INT3', 'INTO', 'BOUNDL', 'BOUNDW',
    'LOOPZ', 'LOOPE', 'LOOPNZ', 'LOOPNE', 'SETO', 'SETNO', 'SETNAE', 'SETNB',
    'SETZ', 'SETNZ', 'SETNA', 'SETNBE', 'SETS', 'SETNS', 'SETP', 'SETPE', 'SETNP',
    'SETPO', 'SETNGE', 'SETNL', 'SETNG', 'SETNLE', 'ARPL', 'LAR', 'LGDT', 'LIDT',
    'LLDT', 'LMSW', 'LSL', 'LTR', 'SGDT', 'SIDT', 'SLDT', 'SMSW', 'STR', 'VERR', 'VERW',
    'FABS', 'FBLD', 'FBSTP', 'FCLEX', 'FNCLEX',
    'FCOS', 'FDECSTP', 'FDISI', 'FNDISI',
    'FDIVR', 'FENI', 'FNENI', 'FFREE', 'FIADD', 'FICOM', 'FICOMP',
    'FIDIVR', 'FIMUL', 'FINCSTP', 'FINIT', 'FNINIT', 'FIST', 'FISTP', 'FISUB',
    'FISUBR', 'FLDCW', 'FLDENV', 'FLDLG2', 'FLDLN2', 'FLDL2E',
    'FLDL2T', 'FLDPI', 'FLDS', 'FLDZ', 'FNOP', 'FPATAN',
    'FPREM', 'FPREM1', 'FPTAN', 'FRNDINT', 'FRSTOR', 'FSAVE', 'FNSAVE',
    'FSCALE', 'FSETPM', 'FSIN', 'FSINCOS', 'FSQRT', 'FST', 'FSTCW', 'FNSTCW',
    'FSTENV', 'FNSTENV', 'FSTSW', 'FNSTSW', 'FTST', 'FUCOM', 'FUCOMP',
    'FUCOMPP', 'FWAIT', 'FXAM', 'FXTRACT', 'FYL2X', 'FYL2XP1', 'F2XM1',
    'FILDQ', 'FILDS', 'FILDL', 'FLDL', 'FLDT', 'FISTQ', 'FISTS', 'FISTL', 'FSTL', 'FSTS',
    'FSTPS', 'FISTPL', 'FSTPL', 'FISTPS', 'FISTPQ', 'FSTPT',
    'FCOMPS', 'FICOMPL', 'FCOMPL', 'FICOMPS',
    'FCOMS', 'FICOML', 'FCOML', 'FICOMS', 'FIADDL', 'FADDL', 'FIADDS',
    'FISUBL', 'FSUBL', 'FISUBS', 'FSUBS', 'FSUBR', 'FSUBRS', 'FISUBRL',
    'FSUBRL', 'FISUBRS', 'FMULS', 'FIMULL', 'FMULL', 'FIMULS', 'FDIVS', 'FIDIVL',
    'FDIVL', 'FIDIVS', 'FDIVRS', 'FIDIVRL', 'FDIVRL', 'FIDIVRS',
    'REPE', 'REPNE', 'FADDS'
  );

type
  tRegister = (
    crNoRegister, crEAX, crECX, crEDX, crEBX, crESP, crEBP, crESI, crEDI,
    crAX, crCX, crDX, crBX, crSP, crBP, crSI, crDI,
    crAL, crCL, crDL, crBL, crAH, crCH, crDH, crBH,

    crDefaultSeg, crCS, crDS, crES, crFS, crGS, crSS,

    crST, crST0, crST1, crST2, crST3, crST4, crST5, crST6, crST7,
    crCR0, crCR1, crCR2, crCR3,

    crEFlags
  );
  tRegisterSet = set of tRegister;

  tResultFlags = (
    cfEqual, cfNotEqual, cfGreater, cfLess, cfGreaterEqual, cfLessEqual,
    cfCarry, cfNoCarry, cfAbove, cfBelow, cfAboveEqual, cfBelowEqual
  );

  tOperandLocation = (
    clNone, clRegister, clFpuStack, clFlags, clSymbol, clMemory, clImmediate,
    clSegmentRegister, clOffset, clInvalid, clCRx
  );

  tSize = (
    csDefault, csByte, csWord, csDWord, csPWORD, csQWord, csTByte, csFar, csNear
  );

  pReference = ^tReference;

  tReference = record
    Segment: tRegister;
    Base: tRegister;
    Index: tRegister;
    Scale: Byte;
    Symbol: pString;
    Offset: LongInt;
    Size: tSize;
  end;

  tByteArr = array [0..65520] of Byte;
  pByteArray = ^tByteArr;
  pDefineValue = ^tDefineValue;
  tDefineValue = record
    DataSize: LongInt;
    Data: pByteArray;
  end;

  pOperand = ^tOperand;
  tOperand = record
    case Location: tOperandLocation of
      clRegister: ( Register: tRegister );
      clFpuStack: ( );
      clFlags: (
          ResultFlag: tResultFlags;
          LabelTrue: pString;
          LabelFalse: pString;
        );
      clSymbol:( LabelName: pString; Offset: LongInt; Size: tSize;
        Symbol: Pointer );
      clMemory: ( Reference: tReference );
      clImmediate: ( Value: LongInt );
  end;

  pAsmInstruction = ^tAsmInstruction;
  tAsmInstruction = object(tObject)
    Prefix: tAsmOp;
    LabelName: pString;
    OpCode: tAsmOp;
    Op1, Op2, Op3: tOperand;
    DefineValue: pDefineValue;
    constructor Create( Operation: tAsmOp);
    constructor Create_Reg( Operation: tAsmOp; _op: tRegister);
    constructor Create_Ref( Operation: tAsmOp; _op: tReference);
    constructor Create_Const( Operation: tAsmOp; _op: LongInt);
    constructor Create_Reg_Reg( Operation: tAsmOp; _op1, _op2: tRegister);
    constructor Create_Reg_Ref( Operation: tAsmOp; _op1: tRegister;
      _op2: tReference);
    constructor Create_Reg_Offset( Operation: tAsmOp; _op1: tRegister;
      _op2: String; ofs: LongInt);
    constructor Create_Ref_Offset( Operation: tAsmOp; _op1: tReference;
      _op2: String; ofs: LongInt);
    constructor Create_Reg_Symbol( Operation: tAsmOp; _op1: tRegister;
      _op2: String);
    constructor Create_Reg_Const( Operation: tAsmOp; _op1: tRegister;
      _op2: LongInt);
    constructor Create_Ref_Reg( Operation: tAsmOp; _op1: tReference;
      _op2: tRegister);
    constructor Create_Ref_Const( Operation: tAsmOp; _op1: tReference;
      _op2: LongInt);
    constructor Create_Reg_Reg_Const( Operation: tAsmOp; _op1, _op2: tRegister;
      _op3: LongInt);
    constructor Create_JSymbol( Operation: tAsmOp; _op: String);
    constructor Create_DB( aValue: pDefineValue);
    constructor CreateInstruction( Operation: tAsmOp; _Op1, _Op2, _Op3: pOperand);
    destructor Done; virtual;
    procedure WriteTo( S: pStream); virtual;
  end;

  pComment = ^tComment;
  tComment = object( tAsmInstruction)
    constructor Create( const Name: String);
    procedure WriteTo( S: pStream); virtual;
  end;

  tOperandTemplate = ( cotInknown, cotReg8, cotReg16, cotReg32, cotSegReg,
    cotMem8, cotMem16, cotMem32, cotMem64, cotMem80, cotMem, cotMem48,
    cotImm8, cotImm16, cotImm32, cotFloatRegister, cotFloatAcc,
    cotDisp8, cotDisp16, cotDisp32, cotDispFar, cotCL, cotAL, cotAX, cotEAX,
    cot1, cotDX, cotCRx
  );

  tInstructionTemplate = record
    AI: tAsmOp;
    OC: Byte;
    IC: LongInt;
    O1, O2, O3: tOperandTemplate;
  end;


const

  TemplatesCount = 896;

  InstructionTemplates: array [0..TemplatesCount - 1] of tInstructionTemplate = (
    (AI: caiAAA; OC: 0; IC: $37),

    (AI: caiAAD; OC: 0; IC:$0AD5),

    (AI: caiAAM; OC: 0; IC:$0AD4),

    (AI: caiAAS; OC: 0; IC:$3F),

    (AI: caiADC; OC: 2; IC: 0; O1: cotAL; O2: cotImm8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotAX; O2: cotImm16),
    (AI: caiADC; OC: 2; IC: 0; O1: cotEAX; O2: cotImm32),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiADC; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiADC; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiADC; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiADC; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiADC; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiADD; OC: 2; IC: 0; O1: cotAL; O2: cotImm8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotAX; O2: cotImm16),
    (AI: caiADD; OC: 2; IC: 0; O1: cotEAX; O2: cotImm32),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiADD; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiADD; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiADD; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiADD; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiADD; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiAND; OC: 2; IC: 0; O1: cotAL; O2: cotImm8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotAX; O2: cotImm16),
    (AI: caiAND; OC: 2; IC: 0; O1: cotEAX; O2: cotImm32),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiAND; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiAND; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiAND; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiAND; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiAND; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiARPL; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiARPL; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),

    (AI: caiBOUND; OC: 2; IC: 0; O1: cotReg16; O2: cotMem),
    (AI: caiBOUND; OC: 2; IC: 0; O1: cotReg32; O2: cotMem),

    (AI: caiBSF; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiBSF; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiBSF; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiBSF; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiBSR; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiBSR; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiBSR; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiBSR; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiBT; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiBT; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiBT; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiBT; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiBT; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiBT; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiBT; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiBT; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiBTC; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiBTC; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiBTC; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiBTC; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiBTC; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiBTC; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiBTC; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiBTC; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiBTR; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiBTR; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiBTR; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiBTR; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiBTR; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiBTR; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiBTR; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiBTR; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiBTS; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiBTS; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiBTS; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiBTS; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiBTS; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiBTS; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiBTS; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiBTS; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiCALL; OC: 1; IC: 0; O1: cotDisp32),
    (AI: caiCALL; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiCALL; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiCALL; OC: 1; IC: 0; O1: cotDispFar),
    (AI: caiCALL; OC: 1; IC: 0; O1: cotMem48),

    (AI: caiCBW; OC: 0; IC: 0),

    (AI: caiCWDE; OC: 0; IC: 0),

    (AI: caiCLC; OC: 0; IC: 0),

    (AI: caiCLD; OC: 0; IC: 0),

    (AI: caiCLI; OC: 0; IC: 0),

    (AI: caiCLTS; OC: 0; IC: 0),

    (AI: caiCMC; OC: 0; IC: 0),

    (AI: caiCMP; OC: 2; IC: 0; O1: cotAL; O2: cotImm8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotAX; O2: cotImm16),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotEAX; O2: cotImm32),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiCMP; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiCMPSB; OC: 0; IC: 0),
    (AI: caiCMPSW; OC: 0; IC: 0),
    (AI: caiCMPSD; OC: 0; IC: 0),

    (AI: caiCWD; OC: 0; IC: 0),

    (AI: caiCDQ; OC: 0; IC: 0),

    (AI: caiDAA; OC: 0; IC: 0),

    (AI: caiDAS; OC: 0; IC: 0),

    (AI: caiDEC; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiDEC; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiDEC; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiDEC; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiDEC; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiDEC; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiDIV; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiDIV; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiDIV; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiDIV; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiDIV; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiDIV; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiENTER; OC: 2; IC: 0; O1: cotImm16; O2: cotImm8),

    (AI: caiF2XM1; OC: 0; IC: 0),

    (AI: caiFABS; OC: 0; IC: 0),

    (AI: caiFADD; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFADD; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFADD; OC: 2; IC: 0; O1: cotFloatAcc; O2: cotFloatRegister),
    (AI: caiFADD; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),

    (AI: caiFADDP; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),
    (AI: caiFADDP; OC: 0; IC: 0),

    (AI: caiFIADD; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFIADD; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiFBLD; OC: 1; IC: 0; O1: cotMem80),

    (AI: caiFBSTP; OC: 1; IC: 0; O1: cotMem80),

    (AI: caiFCHS; OC: 0; IC: 0),

    (AI: caiFCLEX; OC: 0; IC: 0),
    (AI: caiFNCLEX; OC: 0; IC: 0),

    (AI: caiFCOM; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFCOM; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFCOM; OC: 1; IC: 0; O1: cotFloatRegister),
    (AI: caiFCOM; OC: 0; IC: 0),

    (AI: caiFCOMP; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFCOMP; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFCOMP; OC: 1; IC: 0; O1: cotFloatRegister),
    (AI: caiFCOMP; OC: 0; IC: 0),

    (AI: caiFCOMPP; OC: 0; IC: 0),

    (AI: caiFCOS; OC: 0; IC: 0),

    (AI: caiFDECSTP; OC: 0; IC: 0),

    (AI: caiFDIV; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFDIV; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFDIV; OC: 2; IC: 0; O1: cotFloatAcc; O2: cotFloatRegister),
    (AI: caiFDIV; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),

    (AI: caiFDIVP; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),
    (AI: caiFDIVP; OC: 0; IC: 0),

    (AI: caiFIDIV; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFIDIV; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiFDIVR; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFDIVR; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFDIVR; OC: 0; IC: 0),
    (AI: caiFDIVR; OC: 2; IC: 0; O1: cotFloatAcc; O2: cotFloatRegister),
    (AI: caiFDIVR; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),

    (AI: caiFDIVRP; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),
    (AI: caiFDIVRP; OC: 0; IC: 0),

    (AI: caiFIDIVR; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFIDIVR; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiFFREE; OC: 1; IC: 0; O1: cotFloatRegister),

    (AI: caiFICOM; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFICOM; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiFICOMP; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFICOMP; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiFILD; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFILD; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFILD; OC: 1; IC: 0; O1: cotMem64),

    (AI: caiFINCSTP; OC: 0; IC: 0),

    (AI: caiFINIT; OC: 0; IC: 0),
    (AI: caiFNINIT; OC: 0; IC: 0),

    (AI: caiFIST; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFIST; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiFISTP; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFISTP; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFISTP; OC: 1; IC: 0; O1: cotMem64),

    (AI: caiFLD; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFLD; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFLD; OC: 1; IC: 0; O1: cotMem80),
    (AI: caiFLD; OC: 1; IC: 0; O1: cotFloatRegister),

    (AI: caiFLD1; OC: 0; IC: 0),

    (AI: caiFLDL2T; OC: 0; IC: 0),

    (AI: caiFLDL2E; OC: 0; IC: 0),

    (AI: caiFLDPI; OC: 0; IC: 0),

    (AI: caiFLDLG2; OC: 0; IC: 0),

    (AI: caiFLDLN2; OC: 0; IC: 0),

    (AI: caiFLDZ; OC: 0; IC: 0),

    (AI: caiFLDCW; OC: 1; IC: 0; O1: cotMem16),

    (AI: caiFLDENV; OC: 1; IC: 0; O1: cotMem),

    (AI: caiFMUL; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFMUL; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFMUL; OC: 2; IC: 0; O1: cotFloatAcc; O2: cotFloatRegister),
    (AI: caiFMUL; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),

    (AI: caiFMULP; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),
    (AI: caiFMULP; OC: 0; IC: 0),

    (AI: caiFIMUL; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFIMUL; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiFNOP; OC: 0; IC: 0),

    (AI: caiFPATAN; OC: 0; IC: 0),

    (AI: caiFPREM; OC: 0; IC: 0),

    (AI: caiFPREM1; OC: 0; IC: 0),

    (AI: caiFPTAN; OC: 0; IC: 0),

    (AI: caiFRNDINT; OC: 0; IC: 0),

    (AI: caiFRSTOR; OC: 1; IC: 0; O1: cotMem),

    (AI: caiFSAVE; OC: 1; IC: 0; O1: cotMem),

    (AI: caiFNSAVE; OC: 1; IC: 0; O1: cotMem),

    (AI: caiFSCALE; OC: 0; IC: 0),

    (AI: caiFSIN; OC: 0; IC: 0),

    (AI: caiFSINCOS; OC: 0; IC: 0),

    (AI: caiFSQRT; OC: 0; IC: 0),

    (AI: caiFST; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFST; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFST; OC: 1; IC: 0; O1: cotFloatRegister),

    (AI: caiFSTP; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFSTP; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFSTP; OC: 1; IC: 0; O1: cotMem80),
    (AI: caiFSTP; OC: 1; IC: 0; O1: cotFloatRegister),

    (AI: caiFSTCW; OC: 1; IC: 0; O1: cotMem16),

    (AI: caiFNSTCW; OC: 1; IC: 0; O1: cotMem16),

    (AI: caiFSTENV; OC: 1; IC: 0; O1: cotMem),

    (AI: caiFNSTENV; OC: 1; IC: 0; O1: cotMem),

    (AI: caiFSTSW; OC: 1; IC: 0; O1: cotMem16),

    (AI: caiFSTSW; OC: 1; IC: 0; O1: cotAX),

    (AI: caiFNSTSW; OC: 1; IC: 0; O1: cotMem16),

    (AI: caiFNSTSW; OC: 1; IC: 0; O1: cotAX),

    (AI: caiFSUB; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFSUB; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFSUB; OC: 2; IC: 0; O1: cotFloatAcc; O2: cotFloatRegister),
    (AI: caiFSUB; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),

    (AI: caiFSUBP; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),
    (AI: caiFSUB; OC: 0; IC: 0),

    (AI: caiFISUB; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFISUB; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiFSUBR; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiFSUBR; OC: 1; IC: 0; O1: cotMem64),
    (AI: caiFSUBR; OC: 2; IC: 0; O1: cotFloatAcc; O2: cotFloatRegister),
    (AI: caiFSUBR; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),

    (AI: caiFSUBRP; OC: 2; IC: 0; O1: cotFloatRegister; O2: cotFloatAcc),
    (AI: caiFSUBRP; OC: 0; IC: 0),

    (AI: caiFISUBR; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiFISUBR; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiFTST; OC: 0; IC: 0),

    (AI: caiFUCOM; OC: 1; IC: 0; O1: cotFloatRegister),
    (AI: caiFUCOM; OC: 0; IC: 0),

    (AI: caiFUCOMP; OC: 1; IC: 0; O1: cotFloatRegister),
    (AI: caiFUCOMP; OC: 0; IC: 0),

    (AI: caiFUCOMPP; OC: 0; IC: 0),

    (AI: caiFWAIT; OC: 0; IC: 0),

    (AI: caiFXAM; OC: 0; IC: 0),

    (AI: caiFXCH; OC: 1; IC: 0; O1: cotFloatRegister),
    (AI: caiFXCH; OC: 0; IC: 0),

    (AI: caiFXTRACT; OC: 0; IC: 0),

    (AI: caiFYL2X; OC: 0; IC: 0),

    (AI: caiFYL2XP1; OC: 0; IC: 0),

    (AI: caiHLT; OC: 0; IC: 0),

    (AI: caiIDIV; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiIDIV; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiIDIV; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiIDIV; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiIDIV; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiIDIV; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiIMUL; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiIMUL; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiIMUL; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiIMUL; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiIMUL; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiIMUL; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiIMUL; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiIMUL; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiIMUL; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiIMUL; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),
    (AI: caiIMUL; OC: 3; IC: 0; O1: cotReg16; O2: cotReg16; O3: cotImm8),
    (AI: caiIMUL; OC: 3; IC: 0; O1: cotReg32; O2: cotReg32; O3: cotImm8),
    (AI: caiIMUL; OC: 3; IC: 0; O1: cotReg16; O2: cotMem16; O3: cotImm8),
    (AI: caiIMUL; OC: 3; IC: 0; O1: cotReg32; O2: cotMem32; O3: cotImm8),
    (AI: caiIMUL; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiIMUL; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiIMUL; OC: 3; IC: 0; O1: cotReg16; O2: cotReg16; O3: cotImm16),
    (AI: caiIMUL; OC: 3; IC: 0; O1: cotReg32; O2: cotReg32; O3: cotImm32),
    (AI: caiIMUL; OC: 3; IC: 0; O1: cotReg16; O2: cotMem16; O3: cotImm16),
    (AI: caiIMUL; OC: 3; IC: 0; O1: cotReg32; O2: cotMem32; O3: cotImm32),
    (AI: caiIMUL; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiIMUL; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),

    (AI: caiIN; OC: 2; IC: 0;  O1: cotAL; O2: cotImm8),
    (AI: caiIN; OC: 2; IC: 0;  O1: cotAX; O2: cotImm8),
    (AI: caiIN; OC: 2; IC: 0;  O1: cotEAX; O2: cotImm8),
    (AI: caiIN; OC: 2; IC: 0;  O1: cotAL; O2: cotDX),
    (AI: caiIN; OC: 2; IC: 0;  O1: cotAX; O2: cotDX),
    (AI: caiIN; OC: 2; IC: 0;  O1: cotEAX; O2: cotDX),

    (AI: caiINC; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiINC; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiINC; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiINC; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiINC; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiINC; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiINSB; OC: 0; IC: 0),
    (AI: caiINSW; OC: 0; IC: 0),
    (AI: caiINSD; OC: 0; IC: 0),

    (AI: caiINT; OC: 1; IC: 0; O1: cotImm8),
    (AI: caiINTO; OC: 0; IC: 0),

    (AI: caiIRET; OC: 0; IC: 0),

    (AI: caiJA; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJA; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJAE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJAE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJB; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJB; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJBE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJBE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJC; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJC; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJCXZ; OC: 1; IC: 0; O1: cotDisp8),

    (AI: caiJECXZ; OC: 1; IC: 0; O1: cotDisp8),

    (AI: caiJE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJG; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJG; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJGE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJGE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJL; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJL; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJLE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJLE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNA; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNA; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNAE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNAE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNB; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNB; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNBE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNBE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNC; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNC; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNG; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNG; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNGE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNGE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNL; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNL; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNLE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNLE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNO; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNO; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNP; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNP; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNS; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNS; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJNZ; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJNZ; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJO; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJO; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJP; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJP; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJPE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJPE; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJPO; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJPO; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJS; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJS; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJZ; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJZ; OC: 1; IC: 0; O1: cotDisp32),

    (AI: caiJMP; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiJMP; OC: 1; IC: 0; O1: cotDisp32),
    (AI: caiJMP; OC: 1; IC: 0; O1: cotDispFar),
    (AI: caiJMP; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiJMP; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiJMP; OC: 1; IC: 0; O1: cotMem48),

    (AI: caiLAHF; OC: 0; IC: 0),

    (AI: caiLAR; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiLAR; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiLAR; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiLAR; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiLEA; OC: 2; IC: 0; O1: cotReg32; O2: cotMem),

    (AI: caiLEAVE; OC: 0; IC: 0),

    (AI: caiLMSW; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiLMSW; OC: 1; IC: 0; O1: cotMem16),

    (AI: caiLOCK; OC: 0; IC: 0),

    (AI: caiLODSB; OC: 0; IC: 0),

    (AI: caiLODSW; OC: 0; IC: 0),

    (AI: caiLODSD; OC: 0; IC: 0),

    (AI: caiLOOP; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiLOOPE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiLOOPZ; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiLOOPNE; OC: 1; IC: 0; O1: cotDisp8),
    (AI: caiLOOPNZ; OC: 1; IC: 0; O1: cotDisp8),

    (AI: caiLSL; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiLSL; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiLSL; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiLSL; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiLTR; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiLTR; OC: 1; IC: 0; O1: cotMem16),

    (AI: caiMOV; OC: 2; IC: 0; O1: cotAL; O2: cotMem8),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotAX; O2: cotMem16),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotEAX; O2: cotMem32),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem8; O2: cotAL),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem16; O2: cotAX),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem32; O2: cotEAX),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg16; O2: cotSegReg),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotMem16; O2: cotSegReg),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotSegReg; O2: cotReg16),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotSegReg; O2: cotMem16),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotReg32; O2: cotCRx),
    (AI: caiMOV; OC: 2; IC: 0; O1: cotCRx; O2: cotReg32),

    (AI: caiMOVSB; OC: 0; IC: 0),

    (AI: caiMOVSW; OC: 0; IC: 0),

    (AI: caiMOVSD; OC: 0; IC: 0),

    (AI: caiMOVSX; OC: 2; IC: 0; O1: cotReg16; O2: cotReg8),
    (AI: caiMOVSX; OC: 2; IC: 0; O1: cotReg16; O2: cotMem8),
    (AI: caiMOVSX; OC: 2; IC: 0; O1: cotReg32; O2: cotReg8),
    (AI: caiMOVSX; OC: 2; IC: 0; O1: cotReg32; O2: cotMem8),
    (AI: caiMOVSX; OC: 2; IC: 0; O1: cotReg32; O2: cotReg16),
    (AI: caiMOVSX; OC: 2; IC: 0; O1: cotReg32; O2: cotMem16),

    (AI: caiMOVZX; OC: 2; IC: 0; O1: cotReg16; O2: cotReg8),
    (AI: caiMOVZX; OC: 2; IC: 0; O1: cotReg16; O2: cotMem8),
    (AI: caiMOVZX; OC: 2; IC: 0; O1: cotReg32; O2: cotReg8),
    (AI: caiMOVZX; OC: 2; IC: 0; O1: cotReg32; O2: cotMem8),
    (AI: caiMOVZX; OC: 2; IC: 0; O1: cotReg32; O2: cotReg16),
    (AI: caiMOVZX; OC: 2; IC: 0; O1: cotReg32; O2: cotMem16),

    (AI: caiMUL; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiMUL; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiMUL; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiMUL; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiMUL; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiMUL; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiNEG; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiNEG; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiNEG; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiNEG; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiNEG; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiNEG; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiNOP; OC: 0; IC: 0),

    (AI: caiNOT; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiNOT; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiNOT; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiNOT; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiNOT; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiNOT; OC: 1; IC: 0; O1: cotMem32),

    (AI: caiOR; OC: 2; IC: 0; O1: cotAL; O2: cotImm8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotAX; O2: cotImm16),
    (AI: caiOR; OC: 2; IC: 0; O1: cotEAX; O2: cotImm32),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiOR; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiOR; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiOR; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiOR; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiOR; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiOUT; OC: 2; IC: 0;  O1: cotImm8; O2: cotAL),
    (AI: caiOUT; OC: 2; IC: 0;  O1: cotImm8; O2: cotAX),
    (AI: caiOUT; OC: 2; IC: 0;  O1: cotImm8; O2: cotEAX),
    (AI: caiOUT; OC: 2; IC: 0;  O1: cotDX; O2: cotAL),
    (AI: caiOUT; OC: 2; IC: 0;  O1: cotDX; O2: cotAX),
    (AI: caiOUT; OC: 2; IC: 0;  O1: cotDX; O2: cotEAX),

    (AI: caiOUTSB; OC: 0; IC: 0),

    (AI: caiOUTSW; OC: 0; IC: 0),

    (AI: caiOUTSD; OC: 0; IC: 0),

    (AI: caiPOP; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiPOP; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiPOP; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiPOP; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiPOP; OC: 1; IC: 0; O1: cotSegReg),

    (AI: caiPOPA; OC: 0; IC: 0),
    (AI: caiPOPAD; OC: 0; IC: 0),

    (AI: caiPOPF; OC: 0; IC: 0),
    {(AI: caiPOPFD; OC: 0; IC: 0),}

    (AI: caiPUSH; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiPUSH; OC: 1; IC: 0; O1: cotMem32),
    (AI: caiPUSH; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiPUSH; OC: 1; IC: 0; O1: cotReg32),
    (AI: caiPUSH; OC: 1; IC: 0; O1: cotSegReg),
    (AI: caiPUSH; OC: 1; IC: 0; O1: cotImm8),
    (AI: caiPUSH; OC: 1; IC: 0; O1: cotImm16),
    (AI: caiPUSH; OC: 1; IC: 0; O1: cotImm32),

    (AI: caiPUSHA; OC: 0; IC: 0),
    (AI: caiPUSHAD; OC: 0; IC: 0),

    (AI: caiPUSHF; OC: 0; IC: 0),
    (AI: caiPUSHFW; OC: 0; IC: 0),
    (AI: caiPUSHFD; OC: 0; IC: 0),

    (AI: caiRCL; OC: 2; IC: 0; O1: cotReg8; O2: cot1),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotMem8; O2: cot1),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotReg8; O2: cotCL),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotMem8; O2: cotCL),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotReg16; O2: cot1),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotMem16; O2: cot1),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotReg16; O2: cotCL),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotMem16; O2: cotCL),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotReg32; O2: cot1),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotMem32; O2: cot1),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotReg32; O2: cotCL),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotMem32; O2: cotCL),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiRCL; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiRCR; OC: 2; IC: 0; O1: cotReg8; O2: cot1),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotMem8; O2: cot1),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotReg8; O2: cotCL),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotMem8; O2: cotCL),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotReg16; O2: cot1),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotMem16; O2: cot1),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotReg16; O2: cotCL),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotMem16; O2: cotCL),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotReg32; O2: cot1),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotMem32; O2: cot1),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotReg32; O2: cotCL),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotMem32; O2: cotCL),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiRCR; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiROL; OC: 2; IC: 0; O1: cotReg8; O2: cot1),
    (AI: caiROL; OC: 2; IC: 0; O1: cotMem8; O2: cot1),
    (AI: caiROL; OC: 2; IC: 0; O1: cotReg8; O2: cotCL),
    (AI: caiROL; OC: 2; IC: 0; O1: cotMem8; O2: cotCL),
    (AI: caiROL; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiROL; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiROL; OC: 2; IC: 0; O1: cotReg16; O2: cot1),
    (AI: caiROL; OC: 2; IC: 0; O1: cotMem16; O2: cot1),
    (AI: caiROL; OC: 2; IC: 0; O1: cotReg16; O2: cotCL),
    (AI: caiROL; OC: 2; IC: 0; O1: cotMem16; O2: cotCL),
    (AI: caiROL; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiROL; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiROL; OC: 2; IC: 0; O1: cotReg32; O2: cot1),
    (AI: caiROL; OC: 2; IC: 0; O1: cotMem32; O2: cot1),
    (AI: caiROL; OC: 2; IC: 0; O1: cotReg32; O2: cotCL),
    (AI: caiROL; OC: 2; IC: 0; O1: cotMem32; O2: cotCL),
    (AI: caiROL; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiROL; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiROR; OC: 2; IC: 0; O1: cotReg8; O2: cot1),
    (AI: caiROR; OC: 2; IC: 0; O1: cotMem8; O2: cot1),
    (AI: caiROR; OC: 2; IC: 0; O1: cotReg8; O2: cotCL),
    (AI: caiROR; OC: 2; IC: 0; O1: cotMem8; O2: cotCL),
    (AI: caiROR; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiROR; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiROR; OC: 2; IC: 0; O1: cotReg16; O2: cot1),
    (AI: caiROR; OC: 2; IC: 0; O1: cotMem16; O2: cot1),
    (AI: caiROR; OC: 2; IC: 0; O1: cotReg16; O2: cotCL),
    (AI: caiROR; OC: 2; IC: 0; O1: cotMem16; O2: cotCL),
    (AI: caiROR; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiROR; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiROR; OC: 2; IC: 0; O1: cotReg32; O2: cot1),
    (AI: caiROR; OC: 2; IC: 0; O1: cotMem32; O2: cot1),
    (AI: caiROR; OC: 2; IC: 0; O1: cotReg32; O2: cotCL),
    (AI: caiROR; OC: 2; IC: 0; O1: cotMem32; O2: cotCL),
    (AI: caiROR; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiROR; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiREP; OC: 0; IC: 0),
    (AI: caiREPE; OC: 0; IC: 0),
    (AI: caiREPNE; OC: 0; IC: 0),

    (AI: caiRET; OC: 0; IC: 0),
    (AI: caiRET; OC: 1; IC: 0; O1: cotImm8),

    (AI: caiRETF; OC: 0; IC: 0),
    (AI: caiRETF; OC: 1; IC: 0; O1: cotImm8),

    (AI: caiSAHF; OC: 0; IC: 0),

    (AI: caiSAL; OC: 2; IC: 0; O1: cotReg8; O2: cot1),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotMem8; O2: cot1),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotReg8; O2: cotCL),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotMem8; O2: cotCL),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotReg16; O2: cot1),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotMem16; O2: cot1),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotReg16; O2: cotCL),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotMem16; O2: cotCL),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotReg32; O2: cot1),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotMem32; O2: cot1),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotReg32; O2: cotCL),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotMem32; O2: cotCL),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiSAL; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiSAR; OC: 2; IC: 0; O1: cotReg8; O2: cot1),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotMem8; O2: cot1),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotReg8; O2: cotCL),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotMem8; O2: cotCL),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotReg16; O2: cot1),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotMem16; O2: cot1),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotReg16; O2: cotCL),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotMem16; O2: cotCL),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotReg32; O2: cot1),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotMem32; O2: cot1),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotReg32; O2: cotCL),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotMem32; O2: cotCL),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiSAR; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiSHL; OC: 2; IC: 0; O1: cotReg8; O2: cot1),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotMem8; O2: cot1),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotReg8; O2: cotCL),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotMem8; O2: cotCL),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotReg16; O2: cot1),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotMem16; O2: cot1),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotReg16; O2: cotCL),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotMem16; O2: cotCL),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotReg32; O2: cot1),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotMem32; O2: cot1),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotReg32; O2: cotCL),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotMem32; O2: cotCL),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiSHL; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiSHR; OC: 2; IC: 0; O1: cotReg8; O2: cot1),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotMem8; O2: cot1),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotReg8; O2: cotCL),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotMem8; O2: cotCL),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotReg16; O2: cot1),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotMem16; O2: cot1),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotReg16; O2: cotCL),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotMem16; O2: cotCL),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotReg32; O2: cot1),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotMem32; O2: cot1),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotReg32; O2: cotCL),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotMem32; O2: cotCL),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiSHR; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),

    (AI: caiSBB; OC: 2; IC: 0; O1: cotAL; O2: cotImm8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotAX; O2: cotImm16),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotEAX; O2: cotImm32),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiSBB; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiSCASB; OC: 0; IC: 0),

    (AI: caiSCASW; OC: 0; IC: 0),

    (AI: caiSCASD; OC: 0; IC: 0),

    (AI: caiSETA; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETA; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETAE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETAE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETB; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETB; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETBE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETBE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETC; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETC; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETG; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETG; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETGE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETGE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETL; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETL; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETLE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETLE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNA; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNA; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNAE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNAE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNB; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNB; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNBE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNBE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNC; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNC; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNG; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNG; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNGE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNGE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNL; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNL; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNLE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNLE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNO; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNO; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNP; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNP; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNS; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNS; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETNZ; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETNZ; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETO; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETO; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETP; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETP; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETPE; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETPE; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETPO; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETPO; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETS; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETS; OC: 1; IC: 0; O1: cotMem8),
    (AI: caiSETZ; OC: 1; IC: 0; O1: cotReg8),
    (AI: caiSETZ; OC: 1; IC: 0; O1: cotMem8),

    (AI: caiSHLD; OC: 3; IC: 0; O1: cotReg16; O2: cotReg16; O3: cotImm8),
    (AI: caiSHLD; OC: 3; IC: 0; O1: cotMem16; O2: cotReg16; O3: cotImm8),
    (AI: caiSHLD; OC: 3; IC: 0; O1: cotReg16; O2: cotReg16; O3: cotCL),
    (AI: caiSHLD; OC: 3; IC: 0; O1: cotMem16; O2: cotReg16; O3: cotCL),
    (AI: caiSHLD; OC: 3; IC: 0; O1: cotReg32; O2: cotReg32; O3: cotImm8),
    (AI: caiSHLD; OC: 3; IC: 0; O1: cotMem32; O2: cotReg32; O3: cotImm8),
    (AI: caiSHLD; OC: 3; IC: 0; O1: cotReg32; O2: cotReg32; O3: cotCL),
    (AI: caiSHLD; OC: 3; IC: 0; O1: cotMem32; O2: cotReg32; O3: cotCL),

    (AI: caiSHRD; OC: 3; IC: 0; O1: cotReg16; O2: cotReg16; O3: cotImm8),
    (AI: caiSHRD; OC: 3; IC: 0; O1: cotMem16; O2: cotReg16; O3: cotImm8),
    (AI: caiSHRD; OC: 3; IC: 0; O1: cotReg16; O2: cotReg16; O3: cotCL),
    (AI: caiSHRD; OC: 3; IC: 0; O1: cotMem16; O2: cotReg16; O3: cotCL),
    (AI: caiSHRD; OC: 3; IC: 0; O1: cotReg32; O2: cotReg32; O3: cotImm8),
    (AI: caiSHRD; OC: 3; IC: 0; O1: cotMem32; O2: cotReg32; O3: cotImm8),
    (AI: caiSHRD; OC: 3; IC: 0; O1: cotReg32; O2: cotReg32; O3: cotCL),
    (AI: caiSHRD; OC: 3; IC: 0; O1: cotMem32; O2: cotReg32; O3: cotCL),

    (AI: caiSMSW; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiSMSW; OC: 1; IC: 0; O1: cotMem16),

    (AI: caiSTC; OC: 0; IC: 0),

    (AI: caiSTD; OC: 0; IC: 0),

    (AI: caiSTI; OC: 0; IC: 0),

    (AI: caiSTOSB; OC: 0; IC: 0),

    (AI: caiSTOSW; OC: 0; IC: 0),

    (AI: caiSTOSD; OC: 0; IC: 0),

    (AI: caiSUB; OC: 2; IC: 0; O1: cotAL; O2: cotImm8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotAX; O2: cotImm16),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotEAX; O2: cotImm32),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiSUB; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiTEST; OC: 2; IC: 0; O1: cotAL; O2: cotImm8),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotAX; O2: cotImm16),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotEAX; O2: cotImm32),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiTEST; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),

    (AI: caiVERR; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiVERR; OC: 1; IC: 0; O1: cotMem16),
    (AI: caiVERW; OC: 1; IC: 0; O1: cotReg16),
    (AI: caiVERW; OC: 1; IC: 0; O1: cotMem16),

    (AI: caiWAIT; OC: 0; IC: 0),

    (AI: caiXCHG; OC: 2; IC: 0; O1: cotAX; O2: cotReg16),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotReg16; O2: cotAX),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotEAX; O2: cotReg32),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotReg32; O2: cotEAX),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiXCHG; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32),

    (AI: caiXLATB; OC: 0; IC: 0),

    (AI: caiXOR; OC: 2; IC: 0; O1: cotAL; O2: cotImm8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotAX; O2: cotImm16),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotEAX; O2: cotImm32),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg8; O2: cotImm8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg16; O2: cotImm16),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg32; O2: cotImm32),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotMem8; O2: cotImm8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotMem16; O2: cotImm16),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotMem32; O2: cotImm32),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg16; O2: cotImm8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg32; O2: cotImm8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotMem16; O2: cotImm8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotMem32; O2: cotImm8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg8; O2: cotReg8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg16; O2: cotReg16),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg32; O2: cotReg32),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotMem8; O2: cotReg8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotMem16; O2: cotReg16),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotMem32; O2: cotReg32),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg8; O2: cotMem8),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg16; O2: cotMem16),
    (AI: caiXOR; OC: 2; IC: 0; O1: cotReg32; O2: cotMem32)
  );

  RegName: array [tRegister] of String[5] = (
    '', 'EAX', 'ECX', 'EDX', 'EBX', 'ESP', 'EBP', 'ESI', 'EDI',
    'AX', 'CX', 'DX', 'BX', 'SP', 'BP', 'SI', 'DI',
    'AL', 'CL', 'DL', 'BL', 'AH', 'CH', 'DH', 'BH',

    '', 'CS', 'DS', 'ES', 'FS', 'GS', 'SS',

    'ST', 'ST(0)', 'ST(1)', 'ST(2)', 'ST(3)', 'ST(4)', 'ST(5)', 'ST(6)', 'ST(7)',
    'CR0', 'CR1', 'CR2', 'CR3',
    ''
  );

  _Ptr: array [tSize] of String [10] = (
    '', 'byte ptr ', 'word ptr ', 'dword ptr ', 'pword ptr ', 'qword ptr ',
    'tbyte ptr ', 'far ptr ', 'near ptr '
  );

procedure CreateReference( Seg: tRegister; Base: tRegister; Index: tRegister;
  Scale: LongInt; Offset: LongInt; Symbol: pString; Size: tSize; var Ref: tReference);
procedure CopyReference( const Source: tReference; var Dest: tReference);

function IsByteMem( Loc: tOperand): Boolean;
function IsByteReg( Loc: tOperand): Boolean;
function IsWordMem( Loc: tOperand): Boolean;
function IsWordReg( Loc: tOperand): Boolean;
function IsDWordMem( Loc: tOperand): Boolean;
function IsDWordReg( Loc: tOperand): Boolean;
function SizeOfOperand( Operand: tOperand): LongInt;

function IsGeneralReg( Reg: tRegister): Boolean;
function IsSegReg( Reg: tRegister): Boolean;
function IsFPUReg( Reg: tRegister): Boolean;
function IsCRx( Reg: tRegister): Boolean;

procedure AddChars( var Str: String; Len: Byte);

function MakeLabel( AI: pAsmInstruction; LabName: String): pAsmInstruction;

function FindInstruction( AsmOp: tAsmOp; O1, O2, O3: tOperand): LongInt;

function EqualReferences( Ref1, Ref2: tReference): Boolean;

const
  OfsStr: String[7] = 'OFFSET ';

implementation

uses StdLib, Config;

function Operand( Op: tOperand; AddOffs: Boolean): String;
  var
    S: String;
    C: Char;
    I: LongInt;
  begin
    S := '';
    case Op.Location of
      clRegister,
      clSegmentRegister,
      clCRx:
        S := RegName[ Op.Register];
      clFPUStack:
        begin
          if Op.Register = crST then
            Op.Register := crST0;
          I := Pos( '#', _FpuReg_);
          if I > 0 then
            begin
              S := _FpuReg_;
              S[ I] := Chr( Ord( '0') + Ord( Op.Register) - Ord( crSt0));
            end
          else
            S := RegName[ Op.Register]
        end;
      clImmediate:
        Str( Op.Value, S);
      clSymbol:
        begin
          if Op.Size <> csDefault then S := _Ptr[ Op.Size] + ' ';
          if Assigned( Op.LabelName) then S := S + Op.LabelName^;
          if Op.Offset <> 0 then S := S + '+' + ToStr(Op.Offset);
          {if AddOffs then S := _Offset_ + ' ' + S;}
        end;
      clMemory:
      with Op.Reference do
        begin
          S := S + _Ptr[Size] + ' ';
          if NasmSegOverride then
            begin
              S := S + '[';
              if Segment in [crES, crDS, crCS, crSS, crFS, crGS] then
                S := S + RegName[ Segment] + ':';
            end
          else
            begin
              if Segment in [crES, crDS, crCS, crSS, crFS, crGS] then
                S := S + RegName[ Segment] + ':';
              S := S + '[';
            end;
          C := ' ';
          if Base <> crNoRegister then
            begin
              S := S + C + RegName[ Base];
              C := '+';
            end;
          if Index <> crNoRegister then
            begin
              S := S + C + RegName[Index];
              C :='+';
              if Scale <> 1 then S := S + '*'+ ToStr(Scale);
            end;
          if Offset <> 0 then
            begin
              if Offset < 0 then
                S := S + '-' + ToStr( -Offset)
              else
                S := S + C + ToStr( Offset);
              C := '+';
            end;
          if Symbol <> nil then S := S + C + Symbol^;
          S := S + ']';
        end;
      clOffset:
        begin
          S := _Offset_ + ' ' + Op.LabelName^;
          if Op.Offset <> 0 then
            S := S + ' + ' + ToStr( Op.Offset);
        end;
    end;
    Operand := S;
  end;

procedure DisposeOperand( Op: tOperand);
  begin
    if Op.Location = clMemory then
      begin
        if Assigned( Op.Reference.Symbol) then
          begin
          DisposeStr( Op.Reference.Symbol);
          end;
      end
    else if Op.Location in [clSymbol, clOffset] then
      if Assigned( Op.LabelName) then DisposeStr( Op.LabelName);
  end;

function IsFloatComplex( Op: tAsmOp): Boolean;
  begin
    IsFloatComplex := (Op = caiFADD) or (Op = caiFSUB) or (Op = caiFDIV) or
      (Op = caiFDIVR) or (Op = caiFMUL) or (Op = caiFSUBR) or (Op = caiFADDP) or
      (Op = caiFSUBP) or (Op = caiFDIVP) or (Op = caiFDIVRP) or
      (Op = caiFMULP) or (Op = caiFSUBRP);
  end;

function RecodeOperation( Op: tAsmOp): tAsmOp;
  begin
    if Op = caiFADD then
      RecodeOperation := caiFADDP
    else if Op = caiFDIV then
      RecodeOperation := caiFDIVP
    else if Op = caiFDIVR then
      RecodeOperation := caiFDIVRP
    else if Op = caiFMUL then
      RecodeOperation := caiFMULP
    else if Op = caiFSUB then
      RecodeOperation := caiFSUBP
    else if Op = caiFSUBR then
      RecodeOperation := caiFSUBRP
    else
      RecodeOperation := Op;
  end;

constructor tAsmInstruction.Create( Operation: tAsmOp);
  begin
    inherited Init;
    if IsFloatComplex( Operation) then
      begin
        OpCode := RecodeOperation( Operation);
        Op1.Location := clFPUStack;
        Op1.Register := crST1;
        Op2.Location := clFPUStack;
        Op2.Register := crST0;
        Op3.Location := clNone;
      end
    else
      begin
        OpCode := Operation;
        Op1.Location := clNone;
        Op2.Location := clNone;
        Op3.Location := clNone;
      end;
  end;

constructor tAsmInstruction.Create_Reg( Operation: tAsmOp; _op: tRegister);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clRegister;
    Op1.Register := _op;
    Op2.Location := clNone;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Ref( Operation: tAsmOp; _op: tReference);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clMemory;
    Op1.Reference := _op;
    Op2.Location := clNone;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Const( Operation: tAsmOp; _op: LongInt);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clImmediate;
    Op1.Value := _op;
    Op2.Location := clNone;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Reg_Reg( Operation: tAsmOp; _op1, _op2: tRegister);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clRegister;
    Op1.Register := _op1;
    Op2.Location := clRegister;
    Op2.Register := _op2;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Reg_Ref( Operation: tAsmOp; _op1: tRegister;
      _op2: tReference);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clRegister;
    Op1.Register := _op1;
    Op2.Location := clMemory;
    Op2.Reference := _op2;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Reg_Offset( Operation: tAsmOp; _op1: tRegister;
      _op2: String; ofs: LongInt);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clRegister;
    Op1.Register := _op1;
    Op2.Location := clOffset;
    Op2.LabelName := NewStr( _op2);
    Op2.Offset := Ofs;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Ref_Offset( Operation: tAsmOp; _op1: tReference;
      _op2: String; ofs: LongInt);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clMemory;
    Op1.Reference := _op1;
    Op2.Location := clOffset;
    Op2.LabelName := NewStr( _op2);
    Op2.Offset := Ofs;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Reg_Symbol( Operation: tAsmOp; _op1: tRegister;
      _op2: String);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clRegister;
    Op1.Register := _op1;
    Op2.Location := clSymbol;
    Op2.LabelName := NewStr( _op2);
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Reg_Const( Operation: tAsmOp; _op1: tRegister;
      _op2: LongInt);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clRegister;
    Op1.Register := _op1;
    Op2.Location := clImmediate;
    Op2.Value := _op2;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Ref_Reg( Operation: tAsmOp; _op1: tReference;
      _op2: tRegister);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clMemory;
    Op1.Reference := _op1;
    Op2.Location := clRegister;
    Op2.Register := _op2;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Ref_Const( Operation: tAsmOp; _op1: tReference;
      _op2: LongInt);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clMemory;
    Op1 .Reference:= _op1;
    Op2.Location := clImmediate;
    Op2.Value := _op2;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_Reg_Reg_Const( Operation: tAsmOp; _op1, _op2: tRegister;
      _op3: LongInt);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clRegister;
    Op1.Register := _op1;
    Op2.Location := clRegister;
    Op2.Register := _op2;
    Op3.Location := clImmediate;
    Op3.Value := _op3;
  end;

constructor tAsmInstruction.Create_JSymbol( Operation: tAsmOp; _op: String);
  begin
    inherited Init;
    OpCode := Operation;
    Op1.Location := clSymbol;
    Op1.LabelName := NewStr( _op);
    if (Operation <> caiJCXZ) and (Operation <> caiJECXZ) and
      (Operation <> caiCALL) and (Operation <> caiJMP) then
      Op1.Size := csNear
    else
      Op1.Size := csDefault;
    Op2.Location := clNone;
    Op3.Location := clNone;
  end;

constructor tAsmInstruction.Create_DB( aValue: pDefineValue);
  begin
    inherited Init;
    OpCode := caiNoInstruction;
    DefineValue := aValue;
  end;

constructor tAsmInstruction.CreateInstruction( Operation: tAsmOp; _Op1, _Op2, _Op3: pOperand);
  begin
    inherited Init;
    OpCode := Operation;
    if Assigned( _Op1) then
      begin
        Op1 := _Op1^;
        if Op1.Location = clSymbol then
          if (Operation =  caiJZ) or (Operation = caiJNZ) or
            ((Operation >= caiJE) and (Operation <= caiJGE)) or
            (Operation = caiJNO) or
            ((Operation >= caiJNS) and (Operation <= caiJO)) or
            ((Operation >= caiJC) and (Operation <= caiJBE)) or
            ((Operation >= caiJNAE) and (Operation <= caiJNLE)) then
            Op1.Size := csNear;
      end
    else 
      Op1.Location := clNone;
    if Assigned( _Op2) then
      begin
        if _Op2^.Location = clSymbol then
          begin
            Op2.Location := clOffset;
            Op2.LabelName := _Op2^.LabelName;
            Op2.Offset := _Op2^.Offset;
            Op2.Symbol := _Op2^.Symbol;
          end
        else
          Op2 := _Op2^
      end
    else
      Op2.Location := clNone;
    if Assigned( _Op3) then
      Op3 := _Op3^
    else
      Op3.Location := clNone;

    if (Op1.Location = clNone) and IsFloatComplex( Operation) then
      begin
        OpCode := RecodeOperation( Operation);
        Op1.Location := clFPUStack;
        Op1.Register := crST1;
        Op2.Location := clFPUStack;
        Op2.Register := crST0;
        Op3.Location := clNone;
      end;
  end;

destructor tAsmInstruction.Done;
  begin
    if Assigned( LabelName) then
      DisposeStr( LabelName);
    DisposeOperand( Op1);
    DisposeOperand( Op2);
    DisposeOperand( Op3);
    if Assigned( DefineValue) then
      begin
        if Assigned( DefineValue^.Data) then
          FreeMem( DefineValue^.Data, DefineValue^.DataSize);
        Dispose( DefineValue);
      end;
{writeln( opname[opcode]);}
    inherited Done;
  end;

function GetInstructionName( Instruction: tAsmOp): String;
  var
    S: String;
  begin
    {if ExtFloat then}
      GetInstructionName := OpName[ Instruction]
    {else
      begin
        S := '';
        if Instruction = caiFWAIT then
          Instruction := caiWAIT
        else if ((Instruction >= caiFABS) and
          (Instruction <= caiFIDIVRS)) or
          (Instruction = caiFILD) or
          (Instruction = caiFSTP) or
          ((Instruction >= caiFLD) and (Instruction <= caiFIDIV)) or
          (Instruction = caiFDIVRP) or (Instruction = caiFSUBRP) or
          ((Instruction >= caiFCOM) and (Instruction <= caiFNSTS)) then
          begin
            AddChars( S, 16);
            S := OpName[ caiWait] + _EOL_ + S;
          end;
        GetInstructionName := S + OpName[ Instruction];
      end;}
  end;

procedure tAsmInstruction.WriteTo( S: pStream);
  var
    Str: String;
    L: LongInt;
  begin
    {if Assigned( Comment) then
      S^.Write( Comment^[ 1], Length( Comment^) );}

    if Assigned( LabelName) then
      begin
        Str := LabelName^+':'#13#10;
        S^.Write( Str[1], Length(Str));
      end;
    if OpCode = caiNoInstruction then
      begin
        if Assigned( DefineValue) then
          begin
            Str := ' ' + _DB_ + ' ';
            for L := 0 to DefineValue^.DataSize - 1 do
              begin
                Str := Str + ToStr( DefineValue^.Data^[ L]);
                S^.Write( Str[1], Length(Str));
                Str := ',';
              end;
            Str := _EOL_;
            S^.Write( Str[1], Length(Str));
          end;
        Exit;
      end;
    Str := '';
    AddChars( Str, 16);
    if Prefix <> caiNoInstruction then
      Str := Str + OpName[ Prefix] + ' ';
    Str := Str + GetInstructionName( OpCode);
    if Op1.Location <> clNone then
      begin
        AddChars( Str, 32);
        if NasmPush and (OpCode = caiPush) and (Op1.Location = clImmediate) then
          Str := Str + _Ptr[ csDWord] + ' ';

        Str := Str + Operand( Op1, False);
        if Op2.Location <> clNone then
          begin
            if (OpCode = caiLEA) and (Op2.Location = clMemory) then
              Op2.Reference.Size := csDefault;
            Str := Str + ', ' + Operand( Op2, True);
            if Op3.Location <> clNone then
              Str := Str + ', ' + Operand( Op3, True);
          end;
      end;
    Str := Str + _EOL_;
    S^.Write( Str[1] , Length(Str));
  end;


procedure CreateReference( Seg: tRegister; Base: tRegister; Index: tRegister;
  Scale: LongInt; Offset: LongInt; Symbol: pString; Size: tSize;var Ref: tReference);
  begin
    Ref.Segment := Seg;
    Ref.Base := Base;
    Ref.Index := Index;
    Ref.Scale := Scale;
    Ref.Offset := Offset;
    Ref.Symbol := Symbol;
    Ref.Size := Size;
  end;


function IsByteMem( Loc: tOperand): Boolean;
  begin
    IsByteMem := False;
    if (Loc.Location = clMemory) and
      (Loc.Reference.Size = csByte) then
      IsByteMem := True;
  end;

function IsByteReg( Loc: tOperand): Boolean;
  begin
    IsByteReg := False;
    if (Loc.Location = clRegister) and
      (Loc.Register in [crAL, crAH, crBL, crBH, crCL, crCH, crDL, crDH]) then
      IsByteReg := True;
  end;

function IsWordMem( Loc: tOperand): Boolean;
  begin
    IsWordMem := False;
    if (Loc.Location = clMemory) and
      (Loc.Reference.Size = csWord) then
      IsWordMem := True;
  end;

function IsWordReg( Loc: tOperand): Boolean;
  begin
    IsWordReg := False;
    if (Loc.Location = clRegister) and
      (Loc.Register in [crAX, crBX, crCX, crDX, crSI, crDI, crSP, crBP]) then
      IsWordReg := True;
  end;

function IsDWordMem( Loc: tOperand): Boolean;
  begin
    IsDWordMem := False;
    if (Loc.Location = clMemory) and
      (Loc.Reference.Size = csDWord) then
      IsDWordMem := True;
  end;

function IsDWordReg( Loc: tOperand): Boolean;
  begin
    IsDWordReg := False;
    if (Loc.Location = clRegister) and
      (Loc.Register in [crEAX, crEBX, crECX, crEDX, crESI, crEDI, crESP, crEBP]) then
      IsDWordReg := True;
  end;


function SizeOfOperand( Operand: tOperand): LongInt;
  begin
    SizeOfOperand := 0;
    case Operand.Location of
      clRegister,
      clSegmentRegister:
        begin
          case Operand.Register of
            crEAX, crEBX, crECX, crEDX, crEDI, crESI, crEBP, crESP:
              SizeOfOperand := 4;
            crAX, crBX, crCX, crDX, crDI, crSI, crSP, crBP,
            crES, crFS, crGS, crSS, crDS, crCS:
              SizeOfOperand := 2;
            crAL, crAH, crBL, crBH, crCL, crCH, crDl, crDH:
              SizeOfOperand := 1;
          end;
        end;
      clMemory:
        case Operand.Reference.Size of
          csByte:
            SizeOfOperand := 1;
          csWord:
            SizeOfOperand := 2;
          csDWord:
            SizeOfOperand := 4;
          csQWord:
            SizeOfOperand := 8;
          csTByte:
            SizeOfOperand := 10;
        end;
      clSymbol:
        SizeOfOperand := 4;
      clImmediate:
        SizeOfOperand := 4;
    end;
  end;


function IsGeneralReg( Reg: tRegister): Boolean;
  begin
    IsGeneralReg := Reg in [ crEAX..crBH ];
  end;

function IsSegReg( Reg: tRegister): Boolean;
  begin
    IsSegReg := Reg in [ crCS..crSS ];
  end;

function IsFPUReg( Reg: tRegister): Boolean;
  begin
    IsFPUReg := Reg in [ crST .. crST7 ] ;
  end;

function IsCRx( Reg: tRegister): Boolean;
  begin
    IsCRx := (Reg >= crCR0) and (Reg <= crCR3);
  end;


procedure AddChars( var Str: String; Len: Byte);
  begin
    while Length( Str) - Pos( #10, Str) < Len do
      Str := Str + ' ';
  end;


function MakeLabel( AI: pAsmInstruction; LabName: String): pAsmInstruction;
  begin
    if not Assigned( AI^.LabelName) then
      AI^.LabelName := NewStr( LabName);
    MakeLabel := AI;
  end;


function CompatibleOperands( Op: tOperand; OT: tOperandTemplate): Boolean;
  begin
    CompatibleOperands := False;
    case Op.Location of
      clRegister:
        case OT of
          cotAL:
            CompatibleOperands := Op.Register = crAL;
          cotAX:
            CompatibleOperands := Op.Register = crAX;
          cotEAX:
            CompatibleOperands := Op.Register = crEAX;
          cotCL:
            CompatibleOperands := Op.Register = crCL;
          cotDX:
            CompatibleOperands := Op.Register = crDX;
          cotReg32:
            CompatibleOperands := Op.Register in
              [crEAX, crEBX, crECX, crEDX, crESI, crEDI, crESP, crEBP];
          cotReg16:
            CompatibleOperands := Op.Register in
              [crAX, crBX, crCX, crDX, crSI, crDI, crSP, crBP];
          cotReg8:
            CompatibleOperands := Op.Register in
              [crAL, crBL, crCL, crDL, crAH, crBH, crCH, crDH];
        end;

      clSegmentRegister:
        CompatibleOperands := Op.Register in [crES, crDS, crFS, crGS, crSS, crCS];

      clFPUStack:
        case OT of
          cotFloatAcc:
            CompatibleOperands := Op.Register in [crST, crST0];
          cotFloatRegister:
            CompatibleOperands := Op.Register in [crST0..crST7];
        end;

      clImmediate:
        CompatibleOperands := OT in [cotImm8, cotImm16, cotImm32];

      clMemory:
        case OT of
          cotMem32:
            CompatibleOperands := Op.Reference.Size = csDWord;
          cotMem16:
            CompatibleOperands := Op.Reference.Size = csWord;
          cotMem8:
            CompatibleOperands := Op.Reference.Size = csByte;
          cotMem:
            CompatibleOperands := True;
          cotMem64:
            CompatibleOperands := Op.Reference.Size = csQWord;
          cotMem80:
            CompatibleOperands := Op.Reference.Size = csTByte;
          cotMem48:
            CompatibleOperands := Op.Reference.Size = csPWord;
        end;

      clSymbol:
        CompatibleOperands := OT in [cotDisp8, cotDisp16, cotDisp32,
          cotImm32, cotDispFar];

      clOffset:
        CompatibleOperands := OT = cotImm32;

      clCRx:
        CompatibleOperands := OT = cotCRx;
    end;
  end;


function FindInstruction( AsmOp: tAsmOp; O1, O2, O3: tOperand): LongInt;
  var
    I: LongInt;
    IT: tInstructionTemplate;
  begin
    FindInstruction := -1;
    for I := 0 to TemplatesCount - 1 do
      begin
        IT := InstructionTemplates[I];
        if IT.AI = AsmOp then
          begin
            case IT.OC of
              0: if (O1.Location = clNone) then
                begin
                  FindInstruction := I;
                  Exit;
                end;
              1: if CompatibleOperands( O1, It.O1)
                and (O2.Location = clNone) then
                begin
                  FindInstruction := I;
                  Exit;
                end;
              2: if CompatibleOperands( O1, It.O1) and
                  CompatibleOperands( O2, It.O2) and
                  (O3.Location = clNone) then
                begin
                  FindInstruction := I;
                  Exit;
                end;
              3: if CompatibleOperands( O1, It.O1) and
                  CompatibleOperands( O2, It.O2) and
                  CompatibleOperands( O3, It.O3) then
                begin
                  FindInstruction := I;
                  Exit;
                end;
            end;
          end;
      end;
  end;


procedure CopyReference( const Source: tReference; var Dest: tReference);
  begin
    Dest := Source;
    if Assigned( Source.Symbol) then
      Dest.Symbol := NewStr( Source.Symbol^);
  end;


constructor tComment.Create( const Name: String);
  begin
    inherited Create( caiNoInstruction);
    LabelName := NewStr( Name);
  end;

procedure tComment.WriteTo( S: pStream);
  var
    Str: String;
  begin
    Str := '; ';
    if Assigned( LabelName) then
      Str := Str + LabelName^;
    Str := Str + _EOL_;
    S^.Write( Str[1], Length( Str));
  end;


function EqualReferences( Ref1, Ref2: tReference): Boolean;
  begin
    EqualReferences := (Ref1.Base = Ref2.Base) and (Ref1.Index = Ref2.Index) and
      (Ref1.Scale = Ref2.Scale) and (Ref1.Offset = Ref2.Offset) and
      (Ref1.Size = Ref2.Size) and
      ( (not Assigned( Ref1.Symbol) and not Assigned( Ref2.Symbol)) or
      ( Assigned( Ref1.Symbol) and Assigned( Ref2.Symbol) and
      (Ref1.Symbol^ = Ref2.Symbol^) ) );
  end;


end.