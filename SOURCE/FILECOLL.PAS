{-----------------------------------------------------------------------}
{    Pascal Pro                                                         }
{       FileColl unit                                                   }
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

unit FileColl;

interface

uses Dos, Objects;

type

  pFileDateItem = ^tFileDateItem;
  tFileDateItem = record
    FileName: pString;
    DateTime: LongInt;
  end;

  pFileDateCollection = ^tFileDateCollection;
  tFileDateCollection = object( tCollection)
    constructor Load( var S: tStream);
    procedure Store( var S: tStream);
    procedure FreeItem( Item: Pointer); virtual;
    function GetItem(var S: TStream): Pointer; virtual;
    procedure PutItem(var S: TStream; Item: Pointer); virtual;
  end;


  pFileCollection = ^tFileCollection;
  tFileCollection = object( tStringCollection)
    constructor Load( var S: tStream);
    procedure Store( var S: tStream);
  end;


const

  RFileDateCollection: TStreamRec = (
    ObjType: 2000;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tFileDateCollection)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tFileDateCollection);
{$ENDIF}
    Load: @tFileDateCollection.Load;
    Store: @tFileDateCollection.Store
  );

  RFileCollection: TStreamRec = (
    ObjType: 2001;
{$IFDEF TP}
    VmtLink: Ofs(TypeOf(tFileCollection)^);
{$ENDIF}
{$IFDEF PPRO}
    VmtLink: TypeOf(tFileCollection);
{$ENDIF}
    Load: @tFileCollection.Load;
    Store: @tFileCollection.Store
  );

implementation


constructor tFileDateCollection.Load( var S: tStream);
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

procedure tFileDateCollection.Store( var S: tStream); 
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

procedure tFileDateCollection.FreeItem( Item: Pointer);
  begin
    if Assigned( pFileDateItem( Item) ) then
      begin
        if Assigned( pFileDateItem( Item)^.FileName ) then
          DisposeStr( pFileDateItem( Item)^.FileName );
        Dispose( pFileDateItem( Item));
      end;
  end;

function tFileDateCollection.GetItem(var S: TStream): Pointer;
  var
    P: pFileDateItem;
  begin
    New( P);
    P^.FileName := S.ReadStr;
    S.Read( P^.DateTime, SizeOf( P^.DateTime) );
    GetItem := P;
  end;

procedure tFileDateCollection.PutItem(var S: TStream; Item: Pointer);
  begin
    S.WriteStr( pFileDateItem( Item)^.FileName);
    S.Write( pFileDateItem( Item)^.DateTime, SizeOf( LongInt) );
  end;


{ tFileCollection }
constructor tFileCollection.Load( var S: tStream);
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

procedure tFileCollection.Store( var S: tStream); 
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


end.