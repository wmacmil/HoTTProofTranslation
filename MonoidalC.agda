{-# OPTIONS --type-in-type #-}

module MonoidalC where

open import Agda.Primitive renaming (_⊔_ to lmax) public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Unit public
-- open import Agda.Builtin.Nat hiding (_*_; _+_) renaming (Nat to ℕ) public
open import Agda.Builtin.Nat renaming (Nat to ℕ) public
-- open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg public

data ⊥ : Set where

abort : {A : Set} → ⊥ → A
abort ()

¬_ : Set → Set
¬ A = A → ⊥

data TLevel : Set where
  ⟨-2⟩ : TLevel
  suc : (t : TLevel) → TLevel


{- START of Agda hack to write numerals directly -}
instance
  Numℕ : Number ℕ
  Number.Constraint Numℕ _ = ⊤
  Number.fromNat    Numℕ n = n
  NumTLevel : Number TLevel
  Number.Constraint NumTLevel _ = ⊤
  Number.fromNat    NumTLevel k = natToTLevel k
    where
      natToTLevel : ∀ ℕ → {{_ : ⊤}} → TLevel
      natToTLevel 0 = suc (suc ⟨-2⟩)
      natToTLevel (suc n) = suc (natToTLevel n)
  NegTLevel : Negative TLevel
  Negative.Constraint NegTLevel 0 = ⊤
  Negative.Constraint NegTLevel 1 = ⊤
  Negative.Constraint NegTLevel 2 = ⊤
  Negative.Constraint NegTLevel _ = ⊥
  Negative.fromNeg    NegTLevel 0 = suc (suc ⟨-2⟩)
  Negative.fromNeg    NegTLevel 1 = suc ⟨-2⟩
  Negative.fromNeg    NegTLevel 2 = ⟨-2⟩
  Negative.fromNeg    NegTLevel (suc (suc (suc _))) ⦃()⦄
{- END of the Agda hack to write numerals -}


data _≡_ {A : Set} : A → A → Set where
  refl : (a : A) → a ≡ a

infix 1 _≡_ 

_⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
_⁻¹ {A} {x} {.x} (refl .x) = refl x

_∙_ : {A : Set} → {x y : A} → (p : x ≡ y) → {z : A} → (q : y ≡ z) → x ≡ z
_∙_ {x = x} (refl .x) (refl .x) = refl x

ap : {A B : Set} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
ap {A} {B} {x} {.x} f (refl .x) = refl (f x)

id : {X : Set} -> X -> X
id x = x

is-contr : Set → Set
is-contr A = Σ A (λ x → (y : A) → x ≡ y)

has-level : TLevel → Set → Set
has-level ⟨-2⟩ A = is-contr A
has-level (suc n) A = (x y : A) → has-level n (x ≡ y)

is-prop : Set → Set
is-prop = has-level -1

is-set : Set → Set
is-set = has-level 0

-- via wadler's presentation
module ≡-Reasoning {A : Set} where

  infixr 1  _≡⟨_⟩_
  infix  2 _∎

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
    -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  x≡y ∙ y≡z

  _∎ : ∀ (x : A)
    -----
    → x ≡ x
  x ∎  = refl x

open ≡-Reasoning

record Category : Set₁ where
  field
    Obj  : Set
    _=>_ : Obj → Obj → Set
    id=> : {T : Obj} → T => T
    _∘_  : {R S T : Obj} → R => S → S => T → R => T
    lunit : {S T : Obj} (f : S => T) → (id=> {S} ∘ f) ≡ f
    runit : {S T : Obj} (f : S => T) → (f ∘ id=> {T}) ≡ f
    assoc : {Q R S T : Obj} (f : Q => R)(g : R => S)(h : S => T) ->
                    ((f ∘ g) ∘ h) ≡ (f ∘ (g ∘ h))
  assocn : {Q R R' S T : Obj}
            {f  : Q => R} {g : R => S}
            {f' : Q => R'}{g' : R' => S}
            {h : S => T} ->
            (f ∘ g) ≡ (f' ∘ g') ->
            (f ∘ g ∘ h) ≡ (f' ∘ g' ∘ h)
  assocn {f = f} {g = g} {f' = f'} {g' = g'} {h = h} q =
    f ∘ g ∘ h
    ≡⟨ assoc f g h ⁻¹ ⟩
    (f ∘ g) ∘ h
    ≡⟨ ap (λ - → - ∘ h) q ⟩
    -- =⟨ (refl _∘_) =$= (q =$= (refl h)) ⟩ -- why the fuck won't this parse?
    ((f' ∘ g') ∘ h)
    ≡⟨ assoc _ _ _ ⟩
    (f' ∘ g' ∘ h) ∎
  infixr 3 _∘_

_∘ₛ_ : { A B C : Set} → (A → B) → (B → C) → (A → C)
(f ∘ₛ g) x = g (f x)

-- Sets and functions are the classic example of a category.
SET : Category
SET = record
        { Obj = Set
        ; _=>_ = λ X Y → X → Y
        ; id=> = id
        ; _∘_ = _∘ₛ_ --  {!_∘ₛ_!}
        ; lunit = refl
        ; runit = refl
        ; assoc = λ f g h → refl (λ x → h (g (f x)))
        }

lunitm : (f : ⊤ → ⊤) → (λ x → f tt) ≡ f
lunitm f = refl (λ x → tt)

MONOID : Category
MONOID = record
           { Obj = ⊤
           ; _=>_ = λ _ _ → ⊤ → ⊤
           ; id=> = λ _ → tt
           ; _∘_ = λ f g → f ∘ₛ g
           ; lunit = lunitm
           ; runit = lunitm
           ; assoc = λ f g h → refl (λ x → h (g (f x)))
           }

-- define a monoid data type
record Monoid (M : Set) : Set₁ where
  field
    -- Carrier  : Set
    eₘ : M
    _⋆ₘ_ : M → M → M

    lunit : ∀ (m : M) → eₘ ⋆ₘ m ≡ m
    runit : ∀ (m : M) → m ⋆ₘ eₘ ≡ m
    assoc : ∀ (m n p : M) → (m ⋆ₘ n) ⋆ₘ p ≡ m ⋆ₘ n ⋆ₘ p

    MisSet : is-set M

  infixr 3 _⋆ₘ_

variable
  A B C : Set
  x y z w : A
  k l m n : ℕ

-- from Jesper
record Preorder (A : Set) : Set₁ where
  field
    _≤_       : A → A → Set
    ≤-refl    : x ≤ x
    ≤-trans   : x ≤ y → y ≤ z → x ≤ z

module Nat-≤ where

  data _≤_ : ℕ → ℕ → Set where
    ≤-zero :         zero  ≤ n
    ≤-suc  : m ≤ n → suc m ≤ suc n

  ≤-refl : n ≤ n
  ≤-refl {n = zero}  = ≤-zero
  ≤-refl {n = suc k} = ≤-suc ≤-refl

  ≤-trans : k ≤ l → l ≤ m → k ≤ m
  ≤-trans ≤-zero      l≤m         = ≤-zero
  ≤-trans (≤-suc k≤l) (≤-suc l≤m) =
    ≤-suc (≤-trans k≤l l≤m)

-- record SymMonPre (Monoid A) (P : Preorder A) : Set₂ where -- doesn't work, why?
record SymMonPre (P : Preorder A) : Set₂ where
  open Preorder P
  field
    I : A
    _⊗_ : A → A → A
    -- monotone : _≤_ P x z → _≤_ P y w → _≤_ P (x ⊗ y) (z ⊗ w)
    monotone : x ≤ z → y ≤ w →  (x ⊗ y) ≤ (z ⊗ w)
    lunit : I ⊗ x ≡ x
    runit : x ⊗ I ≡ x
    assoc : (x ⊗ y) ⊗ z ≡ x ⊗ y ⊗ z
    sym : x ⊗ y ≡ y ⊗ x

    -- AisSet : is-set A
  infixr 3 _⊗_

PreorderNat : Preorder ℕ
PreorderNat = record { _≤_ = Nat-≤._≤_ ; ≤-refl = Nat-≤.≤-refl ; ≤-trans = Nat-≤.≤-trans }
  -- where
  --   open Nat-≤

module SMPNat where
  -- open SMP {P = PreorderNat}
  open Nat-≤

  n≤n : n Nat-≤.≤ n
  n≤n {n = zero} = Nat-≤.≤-zero
  n≤n {n = suc n} = Nat-≤.≤-suc n≤n

  n≤Sn : n Nat-≤.≤ suc n
  n≤Sn {zero} = Nat-≤.≤-zero
  n≤Sn {suc n} = Nat-≤.≤-suc n≤Sn

  lemma : n Nat-≤.≤ (m + n)
  lemma {n = n} {m = zero} = n≤n
  lemma {n = n} {m = suc m} = Nat-≤.≤-trans (lemma {m = m}) n≤Sn

  postulate
    assoc-+ : {x y z : ℕ} → x + y + z ≡ x + (y + z)
    +-comm : ∀ {m n} → m + n ≡ n + m
    assoc-* : {x y z : ℕ} → x * y * z ≡ x * (y * z)
    *-comm : ∀ {m n} → m * n ≡ n * m
    *-id : {x : ℕ} → x * 1 ≡ x

  monoNat : (x z y w : ℕ) → x ≤ z → y Nat-≤.≤ w → (x + y) Nat-≤.≤ (z + w)
  monoNat .0 z y w ≤-zero q = ≤-trans q lemma
  monoNat (suc m) (suc n) y w (≤-suc p) q = ≤-suc (monoNat m n y w p q)

  +-identityʳ : m + 0 ≡ m
  +-identityʳ {zero} = refl zero
  +-identityʳ {suc m} = ap suc +-identityʳ

  nat+< : SymMonPre PreorderNat  
  nat+< = record
            { I = 0
            ; _⊗_ = _+_
            ; monotone = λ {x} {z} {y} {w} l1 l2 → monoNat x z y w l1 l2
            ; lunit = refl _ --  λ {x} → refl x 
            ; runit = +-identityʳ
            ; assoc = λ {x} {y} {z} → assoc-+ {x} {y} {z}
            ; sym = λ {x} {y} → +-comm {x} {y}
            -- ; AisSet = {!!}
            } 

  mono* : (x z y w : ℕ) → x ≤ z → y ≤ w → (x * y) ≤ (z * w)
  mono* .0 z y w ≤-zero r2 = ≤-zero
  mono* (suc x) (suc z) y w (≤-suc r1) r2 = monoNat y w (x * y) (z * w) r2 (mono* x z y w r1 r2)

  nat*< : SymMonPre PreorderNat  
  nat*< = record
            { I = 1
            ; _⊗_ = _*_
            ; monotone = λ {x} {z} {y} {w} l1 l2 → mono* x z y w l1 l2
            ; lunit = +-identityʳ 
            ; runit = *-id
            ; assoc = λ {x} {y} {z} → assoc-* {x} {y} {z}
            ; sym = λ {x} {y} → *-comm {x} {y}
            }

  -- all noise
  -- postulate
  --   +-comm : ∀ {m n} → m + n ≡ n + m

  -- asdf : m ≤ n → n ≡ k → m ≤ k
  -- asdf {m} {n} {.n} l (refl .n) = l

  -- ≤-comm : (m + n) ≤ (n + m)
  -- ≤-comm {m} {n} = asdf ≤-refl (+-comm {m} {n})

  -- lemma' : suc n ≤ (m + suc n)
  -- lemma' {n = n} {m = m} = ≤-trans (≤-suc (lemma {n} {m})) (≤-trans (≤-suc (≤-comm {m} {n})) (≤-comm {suc n} {m}))

  -- monoNat : (x z y w : ℕ) → x ≤ z → y Nat-≤.≤ w → (x + y) Nat-≤.≤ (z + w)
  -- monoNat .0 z .0 w Nat-≤.≤-zero Nat-≤.≤-zero = Nat-≤.≤-zero
  -- monoNat .0 z (suc m) (suc n) Nat-≤.≤-zero (Nat-≤.≤-suc q) = Nat-≤.≤-trans (monoNat 1 1 m n one≤one q) lemma'
  -- monoNat (suc m) (suc n) .0 w (Nat-≤.≤-suc p) Nat-≤.≤-zero = ≤-suc (monoNat m n zero w p ≤-zero)
  -- monoNat (suc m) (suc n) (suc m1) (suc n1) (Nat-≤.≤-suc p) (Nat-≤.≤-suc q) = ≤-suc (monoNat m n (suc m1) (suc n1) p (≤-suc q))

--   -- record SymMonPre (P : Preorder A) : Set₂ where
--   --   field
--   --     I : A
--   --     _⊗_ : A → A → A
--   --     -- monotone : _≤_ P x z → _≤_ P y w → _≤_ P (x ⊗ y) (z ⊗ w)
--   --     monotone : x ≤ z → y ≤ w →  (x ⊗ y) ≤ (z ⊗ w)
--   --     lunit : I ⊗ x ≡ x
--   --     runit : x ⊗ I ≡ x
--   --     assoc : (x ⊗ y) ⊗ z ≡ x ⊗ y ⊗ z
--   --     sym : x ⊗ y ≡ y ⊗ x
--   --     AisSet : is-set A
--   --   infixr 3 _⊗_

--     -- \otimes

-- -- -- ≡⟨ ? ⟩
-- -- -- ?
-- -- -- ≡⟨ ? ⟩
-- -- -- ? ∎
    
