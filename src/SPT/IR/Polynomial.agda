{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial where

-- Polynomial codes for indexed induction–recursion: the codes PN of Ghani,
-- McBride, Nordvall Forsberg and Spahn (Variations on inductive-recursive
-- definitions, MFCS 2017, Def. 22), with indices. A code over an indexed
-- family D asks for a recursive input at an index (var), a constant (con),
-- a dependent sum whose continuation reads the information of its first
-- part (sigma), or a dependent product (pi) (`Poly`). The paper defines its
-- codes together with their information by induction–recursion; here the
-- information is the index of a code, so the codes are an ordinary
-- inductive family, one level up. That index is a variable, and each code
-- carries an identification of it with the information its former computes
-- (`var-along`, `con-along`, `sigma-along`, `pi-along`), so that a model
-- reads the family as a fibration over the information (the paper proof
-- IndexedUniversalIR.md, §1.4). The codes whose identification is refl are
-- written `var`, `con`, `sigma` and `pi` (pattern synonyms), and every
-- definition here matches those. A code acts on an indexed family of small
-- carriers with readouts, giving its arguments and their information
-- (`Family`, `Args`, `info`). A description adds an output (`Description`,
-- `described`); a scheme gives one description at each index (`Scheme`),
-- and rules are the schemes returning types (`Rules`, `scheme`).
-- `Extensionality` is function extensionality for families of information
-- over the arities.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)

------------------------------------------------------------------------
-- Codes

-- Mathematical shape, with the information of a code as its index W, a
-- variable identified with the information that the former computes:
--
--   var-along i : D i ＝ W → Poly W
--   con-along A : Lift A ＝ W → Poly W
--   sigma-along : Poly X → ((x : X) → Poly (Y x)) → Σ X Y ＝ W → Poly W
--   pi-along A : ((a : A) → Poly (Y a)) → ((a : A) → Y a) ＝ W → Poly W.
--
-- A computed index in place of W would make the family a strict one over
-- the information, which a model of univalent universes does not read as
-- a fibration.

data Poly {ι : Level} (ℓ κ : Level) {I : Set ι} (D : I → Set (ℓ ⊔ κ)) :
  Set (ℓ ⊔ κ) → Set (lsuc (ℓ ⊔ κ) ⊔ ι) where
  var-along : (i : I) {W : Set (ℓ ⊔ κ)} → D i ＝ W → Poly ℓ κ D W
  con-along :
    (A : Set ℓ) {W : Set (ℓ ⊔ κ)} → Lift κ A ＝ W → Poly ℓ κ D W
  sigma-along :
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)} {W : Set (ℓ ⊔ κ)}
    → Poly ℓ κ D X → ((x : X) → Poly ℓ κ D (Y x)) → Σ X Y ＝ W
    → Poly ℓ κ D W
  pi-along :
    (A : Set ℓ) {Y : A → Set (ℓ ⊔ κ)} {W : Set (ℓ ⊔ κ)}
    → ((a : A) → Poly ℓ κ D (Y a)) → ((a : A) → Y a) ＝ W → Poly ℓ κ D W

-- The codes whose identification is refl, with the information their
-- former computes as index.

pattern var i = var-along i refl
pattern con A = con-along A refl
pattern sigma {X} {Y} p q = sigma-along {X} {Y} p q refl
pattern pi A {Y} p = pi-along A {Y} p refl

------------------------------------------------------------------------
-- Families, arguments and information

-- An indexed family of small carriers, each read out into its fiber of D.

record Family {ι : Level} (ℓ κ : Level) {I : Set ι}
  (D : I → Set (ℓ ⊔ κ)) : Set (lsuc ℓ ⊔ κ ⊔ ι) where
  field
    carrier : I → Set ℓ
    readout : (i : I) → carrier i → D i

open Family public

-- The arguments of a code over a family, and the information they return:
-- a recursive input returns its readout, and the continuation of a sum is
-- read at the information of its first argument.

module _ {ι ℓ κ : Level} {I : Set ι} {D : I → Set (ℓ ⊔ κ)} where

  mutual
    Args : {X : Set (ℓ ⊔ κ)} → Poly ℓ κ D X → Family ℓ κ D → Set ℓ
    Args (var i) Z = carrier Z i
    Args (con A) Z = A
    Args (sigma p q) Z = Σ (Args p Z) (λ a → Args (q (info p Z a)) Z)
    Args (pi A p) Z = (a : A) → Args (p a) Z

    info :
      {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ D X) (Z : Family ℓ κ D) → Args p Z
      → X
    info (var i) Z a = readout Z i a
    info (con A) Z a = lift a
    info (sigma p q) Z (a , b) = info p Z a , info (q (info p Z a)) Z b
    info (pi A p) Z f = λ a → info (p a) Z (f a)

------------------------------------------------------------------------
-- Descriptions, schemes and rules

record Description {ι ε : Level} (ℓ κ : Level) {I : Set ι}
  (D : I → Set (ℓ ⊔ κ)) (E : Set ε) : Set (lsuc (ℓ ⊔ κ) ⊔ ι ⊔ ε) where
  field
    Info : Set (ℓ ⊔ κ)
    shape : Poly ℓ κ D Info
    output : Info → E

open Description public

-- A description from a code and an output, its information read off the
-- code.
described :
  {ι ε ℓ κ : Level} {I : Set ι} {D : I → Set (ℓ ⊔ κ)} {E : Set ε}
  {X : Set (ℓ ⊔ κ)} → Poly ℓ κ D X → (X → E) → Description ℓ κ D E
described {X = X} p o = record { Info = X ; shape = p ; output = o }

-- At each index a description returning into that fiber of Data.
record Scheme (ℓ κ : Level) : Set (lsuc (ℓ ⊔ κ)) where
  field
    Index : Set ℓ
    Data : Index → Set (ℓ ⊔ κ)
    rule : (i : Index) → Description ℓ κ Data (Data i)

-- The schemes whose every rule returns a type of level ℓ.
record Rules (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  field
    Index : Set ℓ
    rule :
      (i : Index) → Description ℓ (lsuc ℓ) (λ (_ : Index) → Set ℓ) (Set ℓ)

scheme : {ℓ : Level} → Rules ℓ → Scheme ℓ (lsuc ℓ)
scheme {ℓ} r = record
  { Index = Rules.Index r
  ; Data = λ (_ : Rules.Index r) → Set ℓ
  ; rule = Rules.rule r
  }

------------------------------------------------------------------------
-- Extensionality for families of information

Extensionality : (ℓ κ : Level) → Set (lsuc (ℓ ⊔ κ))
Extensionality ℓ κ = (A : Set ℓ) (Y : A → Set (ℓ ⊔ κ)) → FunExt A Y

-- Extensionality for families of information gives it for families of
-- small types, through lifting.
lowered :
  {ℓ : Level} (κ : Level) → Extensionality ℓ κ → (A : Set ℓ)
  (B : A → Set ℓ) → FunExt A B
lowered κ extensionality A B f g h =
  ap (λ k a → lower (k a))
    ( extensionality A (λ a → Lift κ (B a)) (λ a → lift (f a))
        (λ a → lift (g a)) (λ a → ap lift (h a)))
