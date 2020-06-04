abstract PlTerm = PlType ** {

cat 
  Term ; 

fun 
  
  Pair : Term -> Term -> Term ;
  Fst : Term -> Term
  Snd : Term -> Term
  Nil : Term
 st Cons : Term -> Term -> Term

  TermVar : 

  xX : TermVar ;
  yY : TermVar ;
  zZ : TermVar ;


  Lam : Var -> Typ -> Term -> Term ;


  -- for non-explicit typing
  LamPr : Var -> Term -> Term ;
  


