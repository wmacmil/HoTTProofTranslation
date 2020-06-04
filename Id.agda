
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

-- transport : ∀ {A : Set} (P : A → Set) {x y : A} (p : x ≡ y)  → P x → P y
-- transport {A} P {x} {y} = J D d x y
transport : ∀ {A : Set} {P : A → Set} {x y : A} (p : x ≡ y)  → P x → P y
transport {A} {P} {x} {y} = J D d x y
  where
    D : (x y : A) → x ≡ y → Set
    D x y p =  P x → P y
    d : (x : A) → D x x r
    d = λ x → id

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

-- defn of homotopy
_~_ : {A : Set} {P : A → Set} (f g : (x : A) → P x) → Set
-- _~_ {A} f g = (x : A) → f x ≡ g x
f ~ g  = (x : _) → f x ≡ g x


-- equiv relation
refl~ : {A : Set} {P : A → Set} → ((f : (x : A) → P x) → f ~ f)
refl~ f x = r

sym~ : {A : Set} {P : A → Set} → ((f g : (x : A) → P x) → f ~ g → g ~ f)
sym~ f g fg = λ x → fg x ⁻¹

trans~ : {A : Set} {P : A → Set} → ((f g h : (x : A) → P x) → f ~ g → g ~ h → f ~ h)
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

