{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.General.Discriminator where

-- The rules of Polynomial.General on an explicit algebra, for any
-- extensionality, with no induction–recursion. The code is
-- IR.Description.Indexed.Counter's, which IR.Indexed.General's discriminator
-- reads too (`counter`): a seed at ₀ decoding to 0, and a step taking a child
-- at any index j and landing at the parity of its decoding's successor. The
-- numbers of each parity, with the identification kept, are an algebra
-- (`numbers`). On its generated part an element sits at the index its argument
-- computes, and the decoding equation gives its value (`next`, `next-decodes`,
-- `three-decodes`, `three-lands`). The value also computes at a variable
-- extensionality, since the operation reads only the child (`three-computes`).
-- Induction computes through its equation (`count`, `count-next`,
-- `count-three`), uses the hypothesis at an open child (`count-is-value`), and
-- gives the parity of every index (`parity-of-index`). Counting is the only
-- valuation with its equations, by the initiality of the rule on the generated
-- part (`count-congruent`, `count-unique`). The generated part is exact: an
-- algebra of a code whose only constructor lands at ₀ can be inhabited at ₁
-- (`junk`, `junk-at-₁`), and its generated part has nothing there
-- (`index-is-₀`, `nothing-at-₁`).

open import SPT.Base

open import SPT.IR.Description.Indexed using
  (ι; σ; δ; General; Shape; Mark; general)
open import SPT.IR.Description.Indexed.Counter using
  (parity; counter)
open import SPT.IR.Polynomial using
  (Family; carrier; readout; Args; info; shape; output; Scheme;
   Extensionality)
open import SPT.IR.Polynomial.Algebra using (Algebra)
open import SPT.IR.General using (intro; decoding; Method; ind; ind-β)
open import SPT.IR.Polynomial.General using
  (generated-part; generated-part-computation)
open import SPT.IR.General.Initiality using
  (Congruent; Homomorphic; ind-unique)
open import SPT.IR.Polynomial.General.Initiality using
  (generated-part-initiality)
import SPT.IR.Polynomial.Generated as Generated

------------------------------------------------------------------------
-- An algebra of the counter

-- At each index the numbers of that parity. An argument carries the
-- identification of the index it computes, which is the one its number
-- needs.

numbered : Family lzero lzero (λ (_ : 𝟚) → ℕ)
numbered = record
  { carrier = λ i → Σ ℕ (λ n → parity n ＝ i)
  ; readout = λ i n → pr₁ n
  }

operate :
  (i : 𝟚) → Args (shape (Scheme.rule (general counter) i)) numbered
  → carrier numbered i
operate i ((₀ , x) , c) = 0 , c
operate i ((₁ , j , g , x) , c) = suc (pr₁ (g ⋆)) , c

operate-law :
  (i : 𝟚) (a : Args (shape (Scheme.rule (general counter) i)) numbered)
  → readout numbered i (operate i a)
    ＝ output (Scheme.rule (general counter) i)
        (info (shape (Scheme.rule (general counter) i)) numbered a)
operate-law i ((₀ , x) , refl) = refl
operate-law i ((₁ , j , g , x) , refl) = refl

numbers : Algebra (general counter)
numbers = record
  { family = numbered
  ; operation = operate
  ; law = operate-law
  }

------------------------------------------------------------------------
-- Elements and their decodings

-- An element with the index it sits at.

Element : Set
Element = Σ 𝟚 (Generated.Carrier numbers)

value : Element → ℕ
value e = readout (Generated.generated numbers) (pr₁ e) (pr₂ e)

successor : Element → Shape counter (Generated.generated numbers)
successor e = ₁ , pr₁ e , (λ _ → pr₂ e) , lift ⋆

module _ (extensionality : Extensionality lzero lzero) where

  zeroth : Element
  zeroth =
    ₀ , intro (generated-part counter numbers extensionality) (₀ , lift ⋆)

  zeroth-decodes : value zeroth ＝ 0
  zeroth-decodes =
    decoding (generated-part counter numbers extensionality) (₀ , lift ⋆)

  next : Element → Element
  next e =
    pr₁ (Mark counter (Generated.generated numbers) (successor e)) ,
    intro (generated-part counter numbers extensionality) (successor e)

  next-decodes : (e : Element) → value (next e) ＝ suc (value e)
  next-decodes e =
    decoding (generated-part counter numbers extensionality) (successor e)

  one : Element
  one = next zeroth

  two : Element
  two = next one

  three : Element
  three = next two

  one-decodes : value one ＝ 1
  one-decodes = next-decodes zeroth ∙ ap suc zeroth-decodes

  two-decodes : value two ＝ 2
  two-decodes = next-decodes one ∙ ap suc one-decodes

  three-decodes : value three ＝ 3
  three-decodes = next-decodes two ∙ ap suc two-decodes

  three-lands : pr₁ three ＝ ₁
  three-lands = ap (λ n → parity (suc n)) two-decodes

  -- The operation reads only the child, and split moves only what follows
  -- a recursive input.

  three-computes : value three ＝ 3
  three-computes = refl

------------------------------------------------------------------------
-- Induction

module _ (extensionality : Extensionality lzero lzero) where

  counting : Method (generated-part counter numbers extensionality) (λ i u → ℕ)
  counting (₀ , x) h = 0
  counting (₁ , j , g , x) (k , h) = suc (k ⋆)

  count : Element → ℕ
  count e =
    ind (generated-part counter numbers extensionality) (λ i u → ℕ) counting
      (pr₁ e) (pr₂ e)

  count-zeroth : count (zeroth extensionality) ＝ 0
  count-zeroth =
    ind-β (generated-part counter numbers extensionality) (λ i u → ℕ)
      (generated-part-computation counter numbers extensionality (λ i u → ℕ)
        extensionality)
      counting
      (₀ , lift ⋆)

  count-next :
    (e : Element) → count (next extensionality e) ＝ suc (count e)
  count-next e =
    ind-β (generated-part counter numbers extensionality) (λ i u → ℕ)
      (generated-part-computation counter numbers extensionality (λ i u → ℕ)
        extensionality)
      counting
      (successor e)

  count-three : count (three extensionality) ＝ 3
  count-three =
    count-next (two extensionality)
    ∙ ap suc
        ( count-next (one extensionality)
        ∙ ap suc (count-next (zeroth extensionality) ∙ ap suc count-zeroth))

  -- Agreement at a step is agreement at its one child, which is all that
  -- counting reads; so counting is the only valuation with its equations.

  count-congruent :
    Congruent (generated-part counter numbers extensionality) (λ i u → ℕ)
      counting
  count-congruent (₀ , x) h k r = refl
  count-congruent (₁ , j , g , x) (h , h′) (k , k′) (r , r′) = ap suc (r ⋆)

  count-unique :
    (v : (i : 𝟚) → Generated.Carrier numbers i → ℕ)
    → Homomorphic (generated-part counter numbers extensionality)
        (λ i u → ℕ) v counting
    → (i : 𝟚) (t : Generated.Carrier numbers i)
    → v i t
      ＝ ind (generated-part counter numbers extensionality) (λ i u → ℕ)
          counting i t
  count-unique v equations =
    ind-unique (generated-part counter numbers extensionality)
      (generated-part-initiality counter numbers extensionality) (λ i u → ℕ)
      v counting count-congruent equations

  -- At an open child the hypothesis is what closes the step.

  Agrees : (i : 𝟚) → Generated.Carrier numbers i → Set
  Agrees i u = count (i , u) ＝ value (i , u)

  agreeing : Method (generated-part counter numbers extensionality) Agrees
  agreeing (₀ , x) h = count-zeroth ∙ zeroth-decodes extensionality ⁻¹
  agreeing (₁ , j , g , x) (k , h) =
    count-next (j , g ⋆)
    ∙ (ap suc (k ⋆) ∙ next-decodes extensionality (j , g ⋆) ⁻¹)

  count-is-value : (e : Element) → count e ＝ value e
  count-is-value e =
    ind (generated-part counter numbers extensionality) Agrees agreeing
      (pr₁ e) (pr₂ e)

------------------------------------------------------------------------
-- Decodings have the parity of their index

Parity : (i : 𝟚) → Generated.Carrier numbers i → Set
Parity i u = parity (readout (Generated.generated numbers) i u) ＝ i

module _ (extensionality : Extensionality lzero lzero) where

  parities : Method (generated-part counter numbers extensionality) Parity
  parities (₀ , x) h =
    ap parity (decoding (generated-part counter numbers extensionality) (₀ , x))
  parities (₁ , j , g , x) h =
    ap parity
      (decoding (generated-part counter numbers extensionality)
        (₁ , j , g , x))

  parity-of-index :
    (i : 𝟚) (u : Generated.Carrier numbers i) → Parity i u
  parity-of-index =
    ind (generated-part counter numbers extensionality) Parity parities

------------------------------------------------------------------------
-- Exactness of the identification

seed : General lzero lzero 𝟚 (λ _ → ℕ)
seed = ι (₀ , 0)

-- One point at each index, so an element at ₁ outside the generated part.

single : Family lzero lzero (λ (_ : 𝟚) → ℕ)
single = record
  { carrier = λ _ → 𝟙
  ; readout = λ _ _ → 0
  }

single-law :
  (i : 𝟚) (a : Args (shape (Scheme.rule (general seed) i)) single)
  → readout single i ⋆
    ＝ output (Scheme.rule (general seed) i)
        (info (shape (Scheme.rule (general seed) i)) single a)
single-law i (x , refl) = refl

junk : Algebra (general seed)
junk = record
  { family = single
  ; operation = λ _ _ → ⋆
  ; law = single-law
  }

junk-at-₁ : carrier single ₁
junk-at-₁ = ⋆

module _ (extensionality : Extensionality lzero lzero) where

  index-is-₀ : (i : 𝟚) → Generated.Carrier junk i → i ＝ ₀
  index-is-₀ =
    ind (generated-part seed junk extensionality) (λ i u → i ＝ ₀)
      (λ x h → refl)

  nothing-at-₁ : Generated.Carrier junk ₁ → 𝟘
  nothing-at-₁ t with index-is-₀ ₁ t
  ... | ()
