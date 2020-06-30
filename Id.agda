
module Id where

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

_⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
-- _⁻¹ {A = A} {x} {y} p = J2 D d x y p
_⁻¹ {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = y ≡ x
    d : (a : A) → D a a r
    d a = r


infixr 50 _⁻¹

-- better notation by keeping variables implicit, we loose the ability to
-- utilize eta equality, b/c of how J is defined, perhaps J should have implicit
-- parameters?

_∙_ : {A : Set} → {x y : A} → (p : x ≡ y) → {z : A} → (q : y ≡ z) → x ≡ z
_∙_ {A} {x} {y} p {z} q = J D d x y p z q
    where
    D : (x₁ y₁ : A) → x₁ ≡ y₁ → Set
    D x y p = (z : A) → (q : y ≡ z) → x ≡ z
    d : (z₁ : A) → D z₁ z₁ r
    d = λ v z q → q


infixl 40 _∙_

-- leftId : {A : Set} → (x y : A) → (p : I A x y) → I (I A x y) p (trans x x y r p)
iₗ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ r ∙ p
iₗ {A} {x} {y} p = J D d x y p 
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ≡ r ∙ p
    d : (a : A) → D a a r
    d a = r


-- similairlymeans uniformly substitute the commuted expression throughout the proof.  this applies to all of the proofs
iᵣ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ p ∙ r
iᵣ {A} {x} {y} p = J D d x y p 
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ≡ p ∙ r
    d : (a : A) → D a a r
    d a = r


leftInverse : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ∙ p ≡ r 
leftInverse {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ⁻¹ ∙ p ≡ r
    d : (x : A) → D x x r
    d x = r

rightInverse : {A : Set} {x y : A} (p : x ≡ y) → p ∙ p ⁻¹ ≡ r 
rightInverse {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ∙ p ⁻¹ ≡ r
    d : (a : A) → D a a r
    d a = r

doubleInv : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
doubleInv {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ⁻¹ ⁻¹ ≡ p
    d : (a : A) → D a a r
    d a = r

associativity :{A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r' : z ≡ w ) → p ∙ (q ∙ r') ≡ p ∙ q ∙ r'
associativity {A} {x} {y} {z} {w} p q r' = J D₁ d₁ x y p z w q r'
  where
    D₁ : (x y : A) → x ≡ y → Set
    D₁ x y p = (z w : A) (q : y ≡ z) (r' : z ≡ w ) → p ∙ (q ∙ r') ≡ p ∙ q ∙ r'
    -- d₁ : (x : A) → D₁ x x r 
    -- d₁ x z w q r' = r -- why can it infer this 
    D₂ : (x z : A) → x ≡ z → Set
    D₂ x z q = (w : A) (r' : z ≡ w ) → r ∙ (q ∙ r') ≡ r ∙ q ∙ r'
    D₃ : (x w : A) → x ≡ w → Set
    D₃ x w r' =  r ∙ (r ∙ r') ≡ r ∙ r ∙ r'
    d₃ : (x : A) → D₃ x x r
    d₃ x = r
    d₂ : (x : A) → D₂ x x r
    d₂ x w r' = J D₃ d₃ x w r' 
    d₁ : (x : A) → D₁ x x r
    d₁ x z w q r' = J D₂ d₂ x z q w r'

-- -- the then D₁(x,x,reflₓ) is ... actually shows up in the goal when we have the unfilled hole

-- whiskering
_∙ᵣ_ : {A : Set} → {b c : A} {a : A} {p q : a ≡ b} (α : p ≡ q) (r' : b ≡ c) → p ∙ r' ≡ q ∙ r'
_∙ᵣ_ {A} {b} {c} {a} {p} {q} α r' = J D d b c r' a α
  where
    D : (b c : A) → b ≡ c → Set
    D b c r' = (a : A) {p q : a ≡ b} (α : p ≡ q) → p ∙ r' ≡ q ∙ r'
    d : (a : A) → D a a r
    d a a' {p} {q} α = iᵣ p ⁻¹ ∙ α ∙ iᵣ q

-- iᵣ == ruₚ

_∙ₗ_ : {A : Set} → {a b : A} (q : a ≡ b) {c : A} {r' s : b ≡ c} (β : r' ≡ s) → q ∙ r' ≡ q ∙ s
_∙ₗ_ {A} {a} {b} q {c} {r'} {s} β = J D d a b q c β
  where
    D : (a b : A) → a ≡ b → Set
    D a b q = (c : A) {r' s : b ≡ c} (β : r' ≡ s) → q ∙ r' ≡ q ∙ s
    d : (a : A) → D a a r
    d a a' {r'} {s} β = iₗ r' ⁻¹ ∙ β ∙ iₗ s

_⋆_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
_⋆_ {A} {q = q} {r' = r'} α β = (α ∙ᵣ r') ∙ (q ∙ₗ β)

_⋆'_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
_⋆'_ {A} {p = p} {s = s} α β =  (p ∙ₗ β) ∙ (α ∙ᵣ s)

Ω : {A : Set} (a : A) → Set
Ω {A} a = a ≡ a

Ω² : {A : Set} (a : A) → Set
Ω² {A} a = _≡_ {a ≡ a} r r 

lem1 : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆ β) ≡ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r)
lem1 a α β = r

lem1' : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆' β) ≡  (iₗ r ⁻¹ ∙ β ∙ iₗ r) ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r)
lem1' a α β = r

-- ap\_
apf : {A B : Set} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
apf {A} {B} {x} {y} f p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = {f : A → B} → f x ≡ f y
    d : (x : A) → D x x r
    d = λ x → r 

lem20 : {A : Set} → {a : A} → (α : Ω² {A} a) → (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ≡ α
lem20 α = iᵣ (α) ⁻¹

lem21 : {A : Set} → {a : A} → (β : Ω² {A} a) → (iₗ r ⁻¹ ∙ β ∙ iₗ r) ≡ β
lem21 β = iᵣ (β) ⁻¹

lem2 : {A : Set} → (a : A) → (α β : Ω² {A} a) → (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ≡ (α ∙ β)
lem2 {A} a α β = apf (λ - → - ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ) (lem20 α) ∙ apf (λ - → α ∙ -) (lem21 β)

lem2' : {A : Set} → (a : A) → (α β : Ω² {A} a) → (iₗ r ⁻¹ ∙ β ∙ iₗ r) ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ≡ (β ∙ α )
lem2' {A} a α β =  apf  (λ - → - ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r)) (lem21 β) ∙ apf (λ - → β ∙ -) (lem20 α)
-- apf (λ - → - ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ) (lem20 α) ∙ apf (λ - → α ∙ -) (lem21 β)

⋆≡∙ : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆ β) ≡ (α ∙ β)
⋆≡∙ a α β = lem1 a α β ∙ lem2 a α β

-- proven similairly to above 
⋆'≡∙ : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆' β) ≡ (β ∙ α)
⋆'≡∙ a α β = lem1' a α β ∙ lem2' a α β

-- -- _⋆_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
-- _⋆≡⋆'_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → (α ⋆ β) ≡ (α ⋆' β)
-- _⋆≡⋆'_ {A} {a} {b} {c} {p} {q} {r'} {s} α β = J D d p q α c r' s β
--   where
--     D : (p q : a ≡ b) → p ≡ q → Set
--     D p q α = (c : A) (r' s : b ≡ c) (β : r' ≡ s) → (α ⋆ β) ≡ (α ⋆' β)
--     E : (r' s : b ≡ c) → r' ≡ s → Set
--     -- E p q β = (r ⋆ β) ≡ (r ⋆' β) 
--     E r' s β = (_⋆_ {A} {b = b} {c} {r} {r} {r' = r'} {s = s} r β) ≡ (r ⋆' β)
--     e : ((s : b ≡ c) → E s s r)
--     e r = r
--     d : ((p : a ≡ b) → D p p r)
--     d p c r' s β = {!J E e  !}
--     -- d r r .r r = r

    -- E : (r' s : a ≡ c) → r' ≡ s → Set
    -- E p q β = (_⋆_ {A} {a} {a} {c} {r} {r} {p} {q} r β) ≡ (r ⋆' β)
    -- e : ((pr : a ≡ c) → E pr pr r)
    -- e r = r
    -- d : (x : (a ≡ a)) → D x x r
    -- d = λ x → {!!}

-- _⋆_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
-- _⋆_ {A} {q = q} {r' = r'} α β = (α ∙ᵣ r') ∙ (q ∙ₗ β)


-- eckmannHilton : {A : Set} → (a : A) → (α β : Ω² {A} a) → α ∙ β ≡ β ∙ α 
-- eckmannHilton a α β = {!!} 
--   where
--     l0 : (α ⋆ β) ≡ α ∙ β
--     l0 = ⋆≡∙ a α β
--     l0' : (α ⋆' β) ≡ β ∙ α
--     l0' = ⋆'≡∙ a α β



-- variable 
--   A B C : Set
--   x y z w : A
--   f : A → B
--   g : B → C
--   p : x ≡ y
--   q : y ≡ z

apfHom : {A B : Set} {x y z : A} (p : x ≡ y) (f : A → B) (q : y ≡ z) → apf f (p ∙ q) ≡ (apf f p) ∙ (apf f q)
apfHom {A} {B} {x} {y} {z} p f q = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = {f : A → B} {q : y ≡ z} → apf f (p ∙ q) ≡ (apf f p) ∙ (apf f q)
    d : (x : A) → D x x r
    d x = r

apfInv : {A B : Set} {x y : A} (p : x ≡ y) (f : A → B) → apf f (p ⁻¹) ≡ (apf f p) ⁻¹
apfInv {A} {B} {x} {y} p f = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = {f : A → B} → apf f (p ⁻¹) ≡ (apf f p) ⁻¹
    d : (x : A) → D x x r
    d x = r

-- compostion
infixl 40 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

apfComp : {A B C : Set} {x y : A} (p : x ≡ y) (f : A → B) (g : B → C) → apf g (apf f p) ≡ apf (g ∘ f) p
apfComp {A} {B} {C} {x} {y} p f g = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = {f : A → B} {g : B → C} → apf g (apf f p) ≡ apf (g ∘ f) p
    d : (x : A) → D x x r
    d x = r

id : {A : Set} → A → A
id = λ z → z

-- apfId : {A B : Set} {x y : A} (p : x ≡ y) (f : _≡_ {A}) → apf f p ≡ p

apfId : {A : Set} {x y : A} (p : x ≡ y) → apf id p ≡ p
apfId {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = apf id p ≡ p
    d : (x : A) → D x x r
    d = λ x → r 
--     D x y p = {f : A → B} → apf f (p ⁻¹) ≡ (apf f p) ⁻¹

-- apfHom : {A} {x y z} (p q) : apf (p ∙ q) ≡ apf p ∙ apf q


transport : ∀ {A : Set} {P : A → Set} {x y : A} (p : x ≡ y)  → P x → P y
transport {A} {P} {x} {y} = J D d x y
  where
    D : (x y : A) → x ≡ y → Set
    D x y p =  P x → P y
    d : (x : A) → D x x r
    d = λ x → id

-- all from escardo
-- trans' : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- trans' {x = x} p q = transport {P = λ - → x ≡ - } q p 

-- trans' : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- trans' {x = x} {y = y} {z = z} p q = transport {P = λ - → - ≡ z } (p ⁻¹) q 

-- i think this is the solution escardo's after
-- trans' : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- trans' {x = x} {y = y} {z = z} p q = transport {P = λ _ → x ≡ z } p (transport {P = λ - → x ≡ - } q p) 

-- inv : {A : Set} {x y  : A} → x ≡ y → y ≡ x 
-- inv {x = x} p = transport {P = λ - → - ≡ x} p r

ap : {A B : Set} (f : A → B) (x y : A) → x ≡ y → f x ≡ f y
ap f x y p = transport {P = λ - → f x ≡ f - } p r


-- transport : ∀ {A : Set} (P : A → Set) {x y : A} (p : x ≡ y)  → P x → P y
-- transport {A} P {x} {y} = J D d x y

-- transport' : ∀ {A : Set} {P : A → Set} {x y : A} (p : x ≡ y)  → P x → P y
-- transport' r u = u


p* : {A : Set} {P : A → Set} {x : A} {y : A} {p : x ≡ y} → P x → P y
-- p* {P = P} {p = p} u = transport P p u
p* {P = P} {p = p} u = transport p u

_* : {A : Set} {P : A → Set} {x : A} {y : A} (p : x ≡ y) → P x → P y
(p *) u = transport p u
-- p * u = transport p u

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

_->'_ : Set → Set → Set
-- _->'_ : ?
A ->' B = ((x : A) → B)

arrow : Set₁
arrow = (A B : Set) {b : B} → ((x : A) → B)

constDepType : (A B : Set) → (A → Set)
constDepType A B = λ _ → B

-- transportArrow : {A B : Set} → {x y : A} (p : x ≡ y) → B → B
-- transportArrow {A} {B} p = transport (constDepType A B) p

lift : {A : Set} {P : A → Set} {x y : A}  (u : P x) (p : x ≡ y) → (x , u) ≡ (y , p* {P = P} {p = p} u)
lift {P} u r = r --could use J, but we'll skip the effort for now


-- the type inference needs p below
apd : {A : Set} {P : A → Set} (f : (x : A) → P x) {x y : A} {p : x ≡ y}
  → p* {P = P} {p = p} (f x) ≡ f y
apd {A} {P} f {x} {y} {p} = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p* {P = P} {p = p} (f x) ≡ f y
    d : (x : A) → D x x r
    d = λ x → r

-- the type inference needs p below


-- transportconst : {A B : Set} {x y : A} {p : x ≡ y} (b : B) → transport (constDepType A B) p b ≡ b
-- where P(x) :≡ B
transportconst : {A B : Set} {x y : A} {p : x ≡ y} (b : B) → transport {P = λ _ → B} p b ≡ b
transportconst {A} {B} {x} {y} {p} b = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = transport {P = constDepType A B} p b ≡ b
    d : (x : A) → D x x r
    d = λ x → r

-- 2.3.9

-- problem is we can't avoid keeping the P around to keep the type inference happy
twothreenine : {A : Set} {P : A → Set} {x y z : A}  (p : x ≡ y) (q : y ≡ z ) {u : P x} → ((q *) (_* {P = P} p u)) ≡ (((p ∙ q) *) u)
-- twothreenine : {A : Set} {P : A → Set} {x y z : A}  (p : x ≡ y) (q : y ≡ z ) {u : P x} → ((q *) ((p *) {P = P} u)) ≡ (((p ∙ q) *) u)
twothreenine r r = r

twothreeten : {A B : Set} {f : A → B} {P : B → Set} {x y : A} (p : x ≡ y) {u : P (f x) }  → transport p u ≡ transport {P = P} (apf f p) u 
twothreeten r = r

twothreeeleven : {A : Set} {P Q : A → Set} {f : (x : A) → P x → Q x} {x y : A} (p : x ≡ y) {u : P x} → transport {P = Q} p (f x u) ≡ f y (transport p u)
twothreeeleven r = r

-- 2.4

infixl 20 _~_
-- defn of homotopy
_~_ : {A : Set} {P : A → Set} (f g : (x : A) → P x) → Set
-- _~_ {A} f g = (x : A) → f x ≡ g x
f ~ g  = (x : _) → f x ≡ g x


-- equiv relation
refl~ : {A : Set} {P : A → Set} → ((f : (x : A) → P x) → f ~ f)
refl~ f x = r

sym~ : {A : Set} {P : A → Set} → (f g : (x : A) → P x) → f ~ g → g ~ f
sym~ f g fg = λ x → fg x ⁻¹


-- composite homotopy
trans~ : {A : Set} {P : A → Set} → (f g h : (x : A) → P x) → f ~ g → g ~ h → f ~ h
trans~ f g h fg gh = λ x → (fg x) ∙ (gh x)


-- transrightidentity, note not defitionally equal
translemma : {A : Set} {x y : A} (p : x ≡ y) → p ∙ r ≡ p
translemma r = r

-- first use of implicit non-definitional equality (oudside of the eckmann hilton arguement)
hmtpyNatural : {A B : Set} {f g : A → B} {x y : A} (p : x ≡ y) → ((H : f ~ g) → H x ∙ apf g p ≡ apf f p ∙ H y )
hmtpyNatural {x = x} r H = translemma (H x)

-- via wadler's presentation
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
    -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
    -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
    -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  x≡y ∙ y≡z

  _∎ : ∀ (x : A)
    -----
    → x ≡ x
  x ∎  = r 

open ≡-Reasoning

-- 2.4.4
coroll :  {A B : Set} {f : A → A} {x y : A} (p : x ≡ y) → ((H : f ~ (id {A})) → H (f x) ≡ apf f (H x) )
coroll {A} {f = f} {x = x} p H =
  begin
    H (f x)
  ≡⟨ translemma (H (f x)) ⁻¹ ⟩
    H (f x) ∙ r
  ≡⟨ apf (λ - → H (f x) ∙ -) ll51 ⟩
    H (f x) ∙ (apf (λ z → z) (H x) ∙ H x ⁻¹ )
  ≡⟨ associativity (H (f x)) (apf (λ z → z) (H x)) ((H x ⁻¹)) ⟩
    H (f x) ∙ apf (λ z → z) (H x) ∙ H x ⁻¹ 
  ≡⟨ whisk ⟩
    apf f (H x) ∙ H (x) ∙ H x ⁻¹
  ≡⟨ associativity (apf f (H x)) (H (x)) (H x ⁻¹) ⁻¹ ⟩
    apf f (H x) ∙ (H (x) ∙ H x ⁻¹)
  ≡⟨ apf (λ - → apf f (H x) ∙ -) locallem ⟩
    apf f (H x) ∙ r
  ≡⟨ translemma (apf f (H x)) ⟩
    apf f (H x) ∎
  where 
    thatis : H (f x) ∙ apf (λ z → z) (H x) ≡ apf f (H x) ∙ H (x)
    thatis = hmtpyNatural (H x) H
    whisk : H (f x) ∙ apf (λ z → z) (H x) ∙ H x ⁻¹ ≡ apf f (H x) ∙ H (x) ∙ H x ⁻¹
    whisk = thatis ∙ᵣ (H x ⁻¹)
    locallem :  H x ∙ H x ⁻¹ ≡ r
    locallem = rightInverse (H x)
    ll51 : r ≡ apf (λ z → z) (H x) ∙ H x ⁻¹
    ll51 = locallem ⁻¹ ∙ (apf (λ - → - ∙ H x ⁻¹) (apfId (H x))) ⁻¹

-- Defn. 2.4.6
-- has-inverse in Reijke
qinv : {A B : Set} → (f : A → B) → Set 
qinv {A} {B} f = Σ (B → A) λ g → (f ∘ g ~ id {B}) ×  (g ∘ f ~ id {A})

-- examples

-- 2.4.7

qinvid : {A : Set} → qinv {A} {A} id
qinvid = id , (λ x → r) , λ x → r

-- 2.4.8

p∙ : {A : Set} {x y z : A} (p : x ≡ y) → ((y ≡ z) → (x ≡ z)) 
p∙ p = λ - → p ∙ -

qinvcomp : {A : Set} {x y z : A} (p : x ≡ y) → qinv (p∙ {A} {x} {y} {z} p)
qinvcomp p = (λ - → p ⁻¹ ∙ -) , sec , retr
  where
    sec : (λ x → p∙ p (p ⁻¹ ∙ x)) ~ (λ z → z)
    sec x = 
      begin
        p∙ p (p ⁻¹ ∙ x)
      ≡⟨ associativity p (p ⁻¹) x ⟩
        (p ∙ p ⁻¹) ∙ x
      ≡⟨ apf (λ - → - ∙ x) (rightInverse p) ⟩
        r ∙ x
      ≡⟨ iₗ x ⁻¹ ⟩
        x ∎
    retr : (λ x → p ⁻¹ ∙ p∙ p x) ~ (λ z → z)
    retr x = 
      begin
        p ⁻¹ ∙ p∙ p x
      ≡⟨ associativity (p ⁻¹) p x ⟩
        (p ⁻¹ ∙ p) ∙ x
      ≡⟨ apf (λ - → - ∙ x) (leftInverse p) ⟩
        x ∎

isequiv : {A B : Set} → (f : A → B) → Set 
isequiv {A} {B} f = Σ (B → A) λ g → (f ∘ g ~ id {B}) ×  Σ (B → A) λ g → (g ∘ f ~ id {A})

qinv->isequiv : {A B : Set} → (f : A → B) → qinv f → isequiv f
qinv->isequiv f (g , α , β) = g , α , g , β

-- not the same is as the book, but I can't understand what the book is doing.  maybe this can be a feature
isequiv->qinv : {A B : Set} → (f : A → B) →  isequiv f → qinv f 
isequiv->qinv f (g , α , g' , β ) = (g' ∘ f ∘ g) , sec , retr
  where
    sec : (λ x → f (g' (f (g x)))) ~ (λ z → z)
    sec x = apf f (β (g x)) ∙ α x
      -- begin f (g' (f (g x)))
      --   ≡⟨ apf f (β (g x)) ⟩
      -- f (g x)
      --   ≡⟨ α x ⟩
      -- x ∎
    retr : (λ x → g' (f (g (f x)))) ~ (λ z → z)
    retr x = apf g' (α (f x)) ∙ β x
      -- begin g' (f (g (f x)))
      -- ≡⟨ apf g' (α (f x)) ⟩
      -- g' (f x)
      -- ≡⟨ β x ⟩
      -- x ∎

-- book defn, confusing because of the "let this be the composite homotopy" which mixes both human semantic content as well as formal typing information
isequiv->qinv' : {A B : Set} → (f : A → B) →  isequiv f → qinv f 
isequiv->qinv' f (g , α , h , β ) = g , α , β'
  where
    -- γ : λ x → (trans~ ? ? ? ? ?) x -- trans~ g (g' ∘ f ∘ g) g' ? ? -- {!trans~ g (g' ∘ f ∘ g) g' ? ? !}
    γ : (λ x → g x) ~ λ x → h x 
    γ x = β (g x) ⁻¹ ∙ apf h (α x)
    β' : (λ x → g (f x)) ~ (λ z → z)
    β' x = (γ (f x)) ∙ β x

-- \simeq ≃

_≃_ : (A B : Set) → Set
A ≃ B = Σ (A → B) λ f → isequiv f


≃refl : {A : Set} → A ≃ A
≃refl = (id) , (qi qinvid)
  where
    qi : qinv (λ z → z) → isequiv (λ z → z)
    qi = qinv->isequiv (id )
-- type equivalence is an equivalence relation, 2.4.12
-- qinv->isequiv

-- how to find this in agda automatically?
comm× : {A B : Set} → A × B → B × A
comm× (a , b) = (b , a)

≃sym : {A B : Set} → A ≃ B → B ≃ A
≃sym (f , eqf) = f-1 , ef (f , comm× sndqf)
  where
    qf : isequiv f → qinv f
    qf = isequiv->qinv f 
    f-1 : _ → _
    f-1 = fst (qf eqf)
    sndqf : ((λ x → f (fst (isequiv->qinv f eqf) x)) ~ (λ z → z)) ×
              ((λ x → fst (isequiv->qinv f eqf) (f x)) ~ (λ z → z))
    sndqf = snd (qf eqf)
    ef : qinv f-1 → isequiv f-1
    ef = qinv->isequiv f-1

-- is there any way to make this pattern matching easier
≃trans : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃trans (f , eqf) (g , eqg) = (g ∘ f) , qinv->isequiv (λ z → g (f z)) ((f-1 ∘ g-1) , sec , retr) -- qgf
  where
    qf : isequiv f → qinv f
    qf = isequiv->qinv f
    f-1 = fst (qf eqf)
    qg : isequiv g → qinv g
    qg = isequiv->qinv g
    g-1 = fst (qg eqg)
    sec : (λ x → g (f (f-1 (g-1 x)))) ~ (λ z → z)
    sec x = 
            begin g (f (f-1 (g-1 x)))
            ≡⟨ apf g (fst (snd (qf eqf)) (g-1 x)) ⟩
            g (g-1 x)
            ≡⟨ fst (snd (qg eqg)) x ⟩
            x ∎
    retr : (λ x → f-1 (g-1 (g (f x)))) ~ (λ z → z)
    retr x =
             begin f-1 (g-1 (g (f x)))
             ≡⟨ apf f-1 ((snd (snd (qg eqg)) (f x))) ⟩
             f-1 (f x)
             ≡⟨ snd (snd (qf eqf)) x ⟩
             x ∎


-- 2.6.1
fprodId : {A B : Set} {x y : A × B} → _≡_ {A × B} x y → ((fst x) ≡ (fst y)) × ((snd x) ≡ (snd y))
fprodId p = (apf fst p) , (apf snd p)
-- fprodId r = r , r

-- 2.6.2
equivfprod : {A B : Set} (x y : A × B) → isequiv (fprodId {x = x} {y = y} ) 
equivfprod (x1 , y1) (x2 , y2) = qinv->isequiv fprodId (sn , h1 , h2)
  where
    sn : (x1 ≡ x2) × (y1 ≡ y2) → (x1 , y1) ≡ (x2 , y2)
    sn (r , r) = r
    h1 : (λ x → fprodId (sn x)) ~ (λ z → z)
    h1 (r , r) = r
    -- h1 (r , r) = r
    h2 : (λ x → sn (fprodId x)) ~ (λ z → z)
    h2 r = r

-- 2.6.4
-- alternative name consistent with book, A×B
×fam : {Z : Set} {A B : Z → Set} → (Z → Set)
×fam {A = A} {B = B} z = A z × B z

transport× : {Z : Set} {A B : Z → Set} {z w : Z} (p : z ≡ w) (x : ×fam {Z} {A} {B} z) → (transport p x ) ≡ (transport {Z} {A} p (fst x) , transport {Z} {B} p (snd x))
transport× r s = r

fprod : {A B A' B' : Set} (g : A → A') (h : B → B') → (A × B → A' × B')
fprod g h x = g (fst x) , h (snd x)

-- inverse of fprodId
pair= : {A B : Set} {x y : A × B} → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
pair= (r , r) = r

-- 2.6.5
functorProdEq : {A B A' B' : Set} (g : A → A') (h : B → B')  (x y : A × B) (p : fst x ≡ fst y) (q : snd x ≡ snd y) →  apf (λ - → fprod g h -) (pair= (p , q)) ≡ pair= (apf g p , apf h q)
functorProdEq g h (a , b) (.a , .b) r r = r


-- 2.7.2
-- rename f to g to be consistent with book
equivfDprod : {A : Set} {P : A → Set} (w w' : Σ A (λ x → P x)) → (w ≡ w') ≃ Σ (fst w ≡ fst w') λ p → p* {p = p} (snd w) ≡ snd w'
equivfDprod (w1 , w2) (w1' , w2') = f , qinv->isequiv f (f-1 , ff-1 , f-1f)
  where
    f : (w1 , w2) ≡ (w1' , w2') → Σ (w1 ≡ w1') (λ p → p* {p = p} w2 ≡ w2')
    f r = r , r
    f-1 : Σ (w1 ≡ w1') (λ p → p* {p = p} w2 ≡ w2') → (w1 , w2) ≡ (w1' , w2')
    -- f-1 (r , psndw) = apf (λ - → (w1 , -)) psndw
    f-1 (r , r) = r
    ff-1 : (λ x → f (f-1 x)) ~ (λ z → z)
    ff-1 (r , r) = r
    f-1f : (λ x → f-1 (f x)) ~ (λ z → z)
    f-1f r = r
  
-- 2.7.3
etaDprod : {A : Set} {P : A → Set} (z : Σ A (λ x → P x)) → z ≡ (fst z , snd z)
etaDprod z = r

-- 2.7.4
-- Σfam : {A : Set} {P : A → Set} (Q : Σ A (λ x → P x) → Set) → ((x : A) → Σ (P x) λ u → Q (x , u) )
Σfam : {A : Set} {P : A → Set} (Q : Σ A (λ x → P x) → Set) → (A → Set)
Σfam {P = P} Q x = Σ (P x) λ u → Q (x , u) 

-- inverse of fprodId
-- f-1 : Σ (w1 ≡ w1') (λ p → p* {p = p} w2 ≡ w2') → (w1 , w2) ≡ (w1' , w2')
-- p* {p = fst p} w2)
-- dpair= : {A : Set} {P : A → Set} {w1 w1' : A} {w2 : P w1 } {w2' : P w1'} (p : w1 ≡ w1') →  Σ (w1 ≡ w1') (λ p → p* {p = p} w2 ≡ w2') → (w1 , w2) ≡ (w1' , p* {p = p} w2)
-- dpair= p = {!!}

dpair= : {A : Set} {P : A → Set} {w1 w1' : A} {w2 : P w1 } {w2' : P w1'} →  (p : Σ (w1 ≡ w1') (λ p → p* {p = p} w2 ≡ w2')) → (w1 , w2) ≡ (w1' , w2')
dpair= (r  , r) = r

-- lift : {A : Set} {P : A → Set} {x y : A}  (u : P x) (p : x ≡ y) → (x , u) ≡ (y , p* {P = P} {p = p} u)
-- lift {P} u r = r --could use J, but we'll skip the effort for now

-- transportΣ : {A : Set} {P : A → Set} (Q : Σ A (λ x → P x) → Set) (x y : A) (p : x ≡ y) ((u , z) : Σfam Q x) → p* (u , z) ≡ (p* u  , {!pair=!} (((p , r) *) z)) -- {!!}  )

transportΣ : {A : Set} {P : A → Set} (Q : Σ A (λ x → P x) → Set) (x y : A) (p : x ≡ y) ((u , z) : Σfam Q x)
             →  _* {P = λ - → Σfam Q - } p (u , z) ≡ ((p *) u  , _* {P = λ - → Q ((fst -) , (snd -))} (dpair= (p , r)) z)
transportΣ Q x .x r (u , z) = r -- some agda bug here.  try ctrl-c ctrl-a

-- transportΣ : {A : Set} {P : A → Set} (Q : Σ A (λ x → P x) → Set) (x y : A) (p : x ≡ y) ((u , z) : Σfam Q x) → (p *) (u , z) ≡ ((p *) u  , ((dpair= (p , r)) *) z) -- {!!}  )
-- transportΣ = {!!}

-- _* : {A : Set} {P : A → Set} {x : A} {y : A} (p : x ≡ y) → P x → P y
-- (p *) u = transport p u

-- transportΣ : {Z : Set} {A B : Z → Set} {z w : Z} (p : z ≡ w) (x : ×fam {Z} {A} {B} z) → (transport p x ) ≡ (transport {Z} {A} p (fst x) , transport {Z} {B} p (snd x))


-- begin {!!}
-- ≡⟨ {!!} ⟩
-- {!!}
-- ≡⟨ {!!} ⟩
-- {!!} ∎
