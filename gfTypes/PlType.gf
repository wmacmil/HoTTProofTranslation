abstract PlType = { 

cat 
  Typ ; TypJdg ; TypVar ; Name ; Clas ; S ;
  TypCls;
  ListCls ;
  [Clas]{1};

  -- so should we do a general term language, or have the terms parse under a given type

fun

  -- dunno if I should just delete this
  Eval : TypJdg -> S ;

  TypSig : Name -> TypCls -> Typ -> TypJdg ;

  BaseCls : Clas -> TypVar -> ListCls ; 
  ConsCls : Clas -> ListCls -> ListCls ;

  EmptCls : TypCls ;
  ExtendCls : ListCls -> TypCls -> TypCls ;

  Monad : Clas ;
  Show : Clas ;
  Ord : Clas ;
  Num : Clas ;

  TPair : Typ -> Typ -> Typ ;
  TArr : Typ -> Typ -> Typ ;
  TList : Typ -> Typ ;
  TNat : Typ ;
  TInt : Typ ;
  TString : Typ ;
  TVar1 : TypVar -> Typ -> Typ ;
  TVar : TypVar -> Typ ;

  MkName : String -> Name ;

  -- MkTypVar : String -> TypVar ;
  Xx : TypVar ;
  Yy : TypVar ;
  Zz : TypVar ;


}
