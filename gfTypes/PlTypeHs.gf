--concrete PlTypeHs of PlType = {
concrete PlTypeHs of PlType = open Prelude in {

lincat
  Name = {s : Str} ;
  Typ = Str ;
  TypJdg = {n : Str ; cls : Str ; tys : Str} ;
  TypVar = Str ;
  TypCls = { s : Str } ** { empt : Bool } ;
  Clas =  Str ;
	ListClas = Str ;
	ListCls = { s : Str } ** { v : Str } ;
  S = Str ;

lin

  Eval tj = tj.n ++ "::" ++ tj.cls ++ tj.tys ;

  BaseClas cl = cl ; 
  ConsClas cl lcl = cl ++ "," ++ lcl ; 

  BaseCls cl tv = { s = cl ++ tv ; v = tv } ; 
  ConsCls cl lcl = { s = cl ++ lcl.v ++ "," ++ lcl.s ; v = lcl.v } ;

	-- so should these be lambdas where x is the type variable name to be passed in ?

	TypSig nm tc t = { n = nm.s } 
								   ** {cls = 
												 case tc.empt of {
													 True =>  "" ;
													 False =>  "(" ++ tc.s ++ ")" ++ "=>" 
												 }
											 }
								   ** { tys = t } ;

  EmptCls = { s = "" ; empt = True } ;

	ExtendCls lcl tc = { s = 
													  case tc.empt of {
														  True =>  tc.s ++ lcl.s ;
														  False =>  tc.s ++ "," ++ lcl.s
													  }
												  ; empt = False } ;

  Monad = "Monad" ;
  Num = "Num" ;
  Ord = "Ord" ;
  Num = "Num" ;

  -- Monad = addClass "Monad" ;
  -- Num = addClass "Num" ;
  -- Ord = addClass "Ord" ;
  -- Num = addClass "Num" ;

  TPair t1 t2 = "(" ++ t1 ++ "," ++ t2 ++  ")" ;
  TArr t1 t2 = t1 ++ "->" ++ t2 ;
  TList t1 = "[" ++ t1 ++ "]" ;
  TNat = "Nat" ;
  TInt = "Int" ;
  TString = "String" ;
  TVar1 tv t = tv ++ t ;
	TVar tv = tv ;

  MkName st = { s = st.s } ;

  -- MkTypVar st = st.s ;
  Xx = "x" ;
  Yy = "y" ;
  Zz = "z" ;

 -- oper 
   -- addClass : Str -> Clas ;
	 -- addClass str = lin Clas { s = str ; empt = False } ;
   -- classTyp : Type ;
   -- classTyp = { s : Str ; empt : Bool };

}
