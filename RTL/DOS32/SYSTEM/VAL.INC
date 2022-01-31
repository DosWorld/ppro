{                    GNU LESSER GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Full text of license:
 https://www.gnu.org/licenses/lgpl-3.0.en.html

 (c) Copyright 2022 DosWord
 (c) Copyright 1997-1998 Iggor Khachko - hachko@icl.kazan.su }

procedure Val( const S: String; var L: LongInt; var Code: Integer);
  type
    tValType = (cDec, cHex, cBin);
  var
    L1: LongInt;
    I: Integer;
    VType: tValType;
  begin
    VType := cDec;
    Code := 0;
    if S[0] = #0 then
      Exit;
    I := 1;
    while (S[I] in [' ', #0]) and (I <= Length( S)) do Inc( I);
    L1 := 1;
    if S[I] = '-' then
      begin
        L1 := -1;
        Inc( I);
      end;
    if S[I] = '$' then
      begin
        VType := cHex;
        Inc( I);
      end
    else if S[I] = '%' then
      begin
        VType := cBin;
        Inc( I);
      end;

    case VType of
      cDec:
        begin
          L := 0;
          while I <= Length( S) do
            begin
              if (S[I] < '0') or ( S[I] > '9') then
                begin
                  Code := I;
                  Exit;
                end;
              L := L*10 + Byte( S[I]) - Byte( '0');
              Inc( I);
            end;
        end;
      cHex:
        begin
          L := 0;
          while I <= Length( S) do
            begin
              case S[I] of
                '0'..'9':
                  L := L*16 + Byte( S[I]) - Byte( '0');
                'A'..'F':
                  L := L*16 + Byte( S[I]) - Byte( 'A') + 10;
                'a'..'f':
                  L := L*16 + Byte( S[I]) - Byte( 'a') + 10;
                else
                  begin
                    Code := I;
                    Exit;
                  end;
              end;
              Inc( I);
            end;
        end;
      cBin:
        begin
          L := 0;
          while I <= Length( S) do
            begin
              if (S[I] < '0') or ( S[I] > '1') then
                begin
                  Code := I;
                  Exit;
                end;
              L := L*2 + Byte( S[I]) - Byte( '0');
              Inc( I);
            end;
        end;
    end;
    L := L * L1;
  end;

procedure Val( const S: String; var L: LongInt);
  var
    Code: Integer;
  begin
    Val( S, L, Code);
  end;

procedure Val( const S: String; var I: Integer; var Code: Integer);
  var
    L: LongInt;
  begin
    Val( S, L, Code);
    if Code = 0 then I := L;
  end;

procedure Val( const S: String; var I: Integer);
  var
    Code: Integer;
    L: LongInt;
  begin
    Val( S, L, Code);
    if Code = 0 then I := L;
  end;

procedure Val( const S: String; var SI: ShortInt; var Code: Integer);
  var
    L: LongInt;
  begin
    Val( S, L, Code);
    if Code = 0 then SI := L;
  end;

procedure Val( const S: String; var SI: ShortInt);
  var
    Code: Integer;
    L: LongInt;
  begin
    Val( S, L, Code);
    if Code = 0 then SI := L;
  end;

procedure Val( const S: String; var DW: DWord; var Code: Integer);
  begin
    Val( S, LongInt( DW), Code);
  end;

procedure Val( const S: String; var DW: DWord);
  var
    Code: Integer;
  begin
    Val( S, LongInt( DW), Code);
  end;

procedure Val( const S: String; var W: Word; var Code: Integer);
  var
    L: LongInt;
  begin
    Val( S, L, Code);
    if Code = 0 then W := L;
  end;

procedure Val( const S: String; var W: Word);
  var
    Code: Integer;
    L: LongInt;
  begin
    Val( S, L, Code);
    if Code = 0 then W := L;
  end;

procedure Val( const S: String; var B: Byte; var Code: Integer);
  var
    L: LongInt;
  begin
    Val( S, L, Code);
    if Code = 0 then B := L;
  end;

procedure Val( const S: String; var B: Byte);
  var
    Code: Integer;
    L: LongInt;
  begin
    Val( S, L, Code);
    if Code = 0 then B := L;
  end;


procedure Val( const S: String; var E: Extended; var Code: Integer);
  var
    ChangeSign: Boolean;
    I: Integer;
    Exp, L: LongInt;
  begin
    Code := 0;
    if S[0] = #0 then
      Exit;
    I := 1;
    while (S[I] in [' ', #0]) and (I <= Length( S)) do Inc( I);
    ChangeSign := False;
    if S[I] = '-' then
      begin
        ChangeSign := True;
        Inc( I);
      end;
    Exp := 0;
    E := 0;
    while (I <= Length( S) ) and (S[I] >= '0') and (S[I] <= '9') do
      begin
        E := E * 10 + Ord( S[I]) - Ord( '0');
        Inc( I);
      end;
    if (I <= Length( S) ) and (S[I] = '.') then
      begin
        Inc( I);
        while (I <= Length( S) ) and (S[I] >= '0') and (S[I] <= '9') do
          begin
            E := E * 10 + Ord( S[I]) - Ord( '0');
            Inc( I);
            Dec( Exp);
         end;
      end;
    if (I <= Length( S) ) and ( ( S[I] = 'E' ) or (S[I] = 'e') ) then
      begin
        L := 0;
        Inc( I);
        Val( Copy( S, I, 255), L, Code);
        if Code > 0 then
          begin
            Inc( Code, I - 1);
            Exit;
          end;
        Inc( Exp, L);
        I := Length( S) + 1;
      end;
    if I <= Length( S) then
      begin
        Code := I;
        Exit;
      end;
asm
  @@mylab:
end;
    if Exp > 0 then
      while Exp > 0 do
        begin
          E := E * 10;
          Dec( Exp);
        end
    else if Exp < 0 then
      while Exp < 0 do
        begin
          E := E / 10.0;
          Inc( Exp);
        end;
    if ChangeSign then
      E := -E;
    Code := 0;
  end;

procedure Val( const S: String; var E: Extended);
  var
    Code: Integer;
  begin
    Val( S, E, Code);
  end;

procedure Val( const S: String; var D: Double; var Code: Integer);
  var
    E: Extended;
  begin
    Val( S, E, Code);
    if Code = 0 then D := E;
  end;

procedure Val( const S: String; var D: Double);
  var
    Code: Integer;
    E: Extended;
  begin
    Val( S, E, Code);
    if Code = 0 then D := E;
  end;

procedure Val( const S: String; var Sn: Single; var Code: Integer);
  var
    E: Extended;
  begin
    Val( S, E, Code);
    if Code = 0 then Sn := E;
  end;

procedure Val( const S: String; var Sn: Single);
  var
    Code: Integer;
    E: Extended;
  begin
    Val( S, E, Code);
    if Code = 0 then Sn := E;
  end;

