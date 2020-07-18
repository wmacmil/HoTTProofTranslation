

module question where

open import Agda.Builtin.Sigma public

data _≡_ {A : Set} (a : A) : A → Set where
  r : a ≡ a

infix 20 _≡_

J : {A : Set}
    → (D : (x y : A) → (x ≡ y) →  Set)
    -- → (d : (a : A) → (D a a r ))
    → ((a : A) → (D a a r ))
    → (x y : A)
    → (p : x ≡ y)
    ------------------------------------
    → D x y p
J D d x .x r = d x

-- ap\_
apf : {A B : Set} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
apf {A} {B} {x} {y} f p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = {f : A → B} → f x ≡ f y
    d : (x : A) → D x x r
    d = λ x → r 

id : {A : Set} → A → A
id = λ z → z


-- transport : ∀ {A : Set} {P : A → Set} {x y : A} (p : x ≡ y)  → P x → P y
-- transport {A} {P} {x} {y} = J D d x y
--   where
--     D : (x y : A) → x ≡ y → Set
--     D x y p =  P x → P y
--     d : (x : A) → D x x r
--     d = λ x → id

-- p* : {A : Set} {P : A → Set} {x : A} {y : A} {p : x ≡ y} → P x → P y
-- -- p* {P = P} {p = p} u = transport P p u
-- p* {P = P} {p = p} u = transport p u

-- _* : {A : Set} {P : A → Set} {x : A} {y : A} (p : x ≡ y) → P x → P y
-- (p *) u = transport p u
-- -- p * u = transport p u

transport : ∀ {A : Set} (P : A → Set) {x y : A} (p : x ≡ y)  → P x → P y
transport P r px = px

apd : {A : Set} {P : A → Set} (f : (x : A) → P x) {x y : A} (p : x ≡ y)
      → transport P p (f x) ≡ f y
apd f r = r

-- apd : {A : Set} {P : A → Set} (f : (x : A) → P x) {x y : A} {p : x ≡ y}
--   → p* {P = P} {p = p} (f x) ≡ f y
-- apd {A} {P} f {x} {y} {p} = J D d x y p
--   where
--     D : (x y : A) → x ≡ y → Set
--     D x y p = p* {P = P} {p = p} (f x) ≡ f y
--     d : (x : A) → D x x r
--     d = λ x → r

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

-- 2.6.1
fprodId : {A B : Set} {x y : A × B} → _≡_ {A × B} x y → ((fst x) ≡ (fst y)) × ((snd x) ≡ (snd y))
fprodId p = (apf fst p) , (apf snd p)
-- fprodId r = r , r

-- 2.6.4
-- alternative name consistent with book, A×B
×fam : {Z : Set} {A B : Z → Set} → (Z → Set)
×fam {A = A} {B = B} z = A z × B z

-- transport× : {Z : Set} {A B : Z → Set} {z w : Z} (p : z ≡ w) (x : ×fam {Z} {A} {B} z) → (transport p x ) ≡ (transport {Z} {A} p (fst x) , transport {Z} {B} p (snd x))
-- transport× r s = r

fprod : {A B A' B' : Set} (g : A → A') (h : B → B') → (A × B → A' × B')
fprod g h x = g (fst x) , h (snd x)

-- inverse of fprodId
pair= : {A B : Set} {x y : A × B} → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
pair= (r , r) = r

-- 2.6.5
functorProdEq : {A B A' B' : Set} (g : A → A') (h : B → B')  (x y : A × B) (p : fst x ≡ fst y) (q : snd x ≡ snd y) →  apf (λ - → fprod g h -) (pair= (p , q)) ≡ pair= (apf g p , apf h q)
functorProdEq g h (a , b) (.a , .b) r r = r


  
-- 2.7.3
etaDprod : {A : Set} {P : A → Set} (z : Σ A (λ x → P x)) → z ≡ (fst z , snd z)
etaDprod z = r

-- 2.7.4
Σfam : {A : Set} {P : A → Set} (Q : Σ A (λ x → P x) → Set) → (A → Set)
Σfam {P = P} Q x = Σ (P x) λ u → Q (x , u) 

dpair= : {A : Set} {P : A → Set} {w1 w1' : A} {w2 : P w1 } {w2' : P w1'} →  (p : Σ (w1 ≡ w1') (λ p → transport P p  w2 ≡ w2')) → (w1 , w2) ≡ (w1' , w2')
dpair= (r  , r) = r

-- transportΣ : {A : Set} {P : A → Set} (Q : Σ A (λ x → P x) → Set) (x y : A) (p : x ≡ y) ((u , z) : Σfam Q x)
--              →  _* {P = λ - → Σfam Q - } p (u , z) ≡ ((p *) u  , _* {P = λ - → Q ((fst -) , (snd -))} (dpair= (p , r)) z)
-- transportΣ Q x .x r (u , z) = r -- some agda bug here.  try ctrl-c ctrl-a

fDprod : {A A' : Set} {P : A → Set} {Q : A' → Set} (g : A → A') (h : (a : A) →  P a → Q (g a)) → (Σ A λ a → P a) → (Σ A' λ a' → Q a')
fDprod g h (a , pa) = g a , h a pa

ap2 : {A B C : Set} {x x' : A} {y y' : B} (f : A → B → C)
      → (x ≡ x') → (y ≡ y') → (f x y ≡ f x' y')
ap2 f r r = r


-- apd : {A : Set} {P : A → Set} (f : (x : A) → P x) {x y : A} {p : x ≡ y}
-- → p* {P = P} {p = p} (f x) ≡ f y

-- transport : ∀ {A : Set} {P : A → Set} {x y : A} (p : x ≡ y)  → P x → P y

-- p* : {A : Set} {P : A → Set} {x : A} {y : A} {p : x ≡ y} → P x → P y
-- -- p* {P = P} {p = p} u = transport P p u
-- p* {P = P} {p = p} u = transport p u

transportd : {X : Set } (A : X → Set  ) (B : (x : X) → A x → Set )
  {x : X} ((a , b) : Σ (A x) λ a → B x a) {y : X} (p : x ≡ y)
  → B x a → B y (transport A p a)
transportd A B (a , b) r = id

ap2d : {A : Set} {x x' : A}  {P : A → Set} {y : P x} {y' : P x'} {C : (x : A)
  → P x → Set} (f : (x : A) → (y : P x) → C x y )
  → (p : x ≡ x') → (q : transport P p y ≡ y') → 
  transport (C x') q (transportd P C (y , (f x y)) p (f x y)) ≡ f x' y'
ap2d f r r = r

  -- p* {p = q} (p* {p = p} (λ - → f x -)) y ≡ f x' y'
  -- apd {!(p* {p = p} f x)!} q  ≡ {!f x' y'!}
  -- (p* {p = p} f x)
  -- p* {p = q} (p* {p = p} (f x)) y ≡ {!f x' y'!}
  -- (f x y ≡ f x' y')

-- (.patternInTele0 .patternInTele1 : Σ A P)

functorDProdEq : {A A' : Set} {P : A → Set} {Q : A' → Set} (g : A → A') 
                 (h : (a : A) →  P a → Q (g a))
                 → ((x1 , y1) (x2 , y2) : Σ A λ a → P a)
                 -- → (p : x1 ≡ x2) (q : p* {p = p} y1 ≡ y2)
                 → (p : x1 ≡ x2) (q : transport P p y1 ≡ y2)
                 → apf (λ - → fDprod g h -) (dpair= (p , q))
                 ≡ dpair= ((apf g p , ap2d (λ x y → {!!}) {!!} q ))
functorDProdEq = {!!}
