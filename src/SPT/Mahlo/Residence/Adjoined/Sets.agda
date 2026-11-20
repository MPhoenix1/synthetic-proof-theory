{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Adjoined.Sets where

-- Generated Tarski names and their decodings are sets when the starting
-- and adjoined families are sets, under function extensionality.
-- Shape and Fields unfold each name into its constructor and arguments.
-- The retraction fold-unfold gives uniqueness of identifications by
-- recursion on formation (form-unique, name-is-set, decode-is-set).

open import SPT.Base
open import SPT.Foundation.Propositions using
  (is-proposition; is-set; 𝟘-is-proposition; 𝟙-is-proposition;
   propositions-are-sets)
open import SPT.Foundation.Sets.Uniqueness using
  (Unique; retract-unique; pair-unique; function-unique;
   Extensionality; extensional; Π-is-set)
open import SPT.Foundation.Sets using
  (lifts-of-sets-are-sets; sums-of-sets-are-sets)
open import SPT.Foundation.Hedberg using (𝟚-is-set; ℕ-is-set)
open import SPT.Foundation.Tree.W.Sets using (trees-over-a-set-are-sets)
open import SPT.Mahlo.Residence.Adjoined using
  (Form; emptyᶠ; unitᶠ; twoᶠ; naturalᶠ; productᶠ; sumᶠ; treeᶠ; identityᶠ;
   liftedᶠ; belowᶠ; adjoinedᶠ; Name; decode; empty; unit; two; natural;
   product; sum; tree; identity; lifted; below; adjoined)

------------------------------------------------------------------------
-- The shapes of names

data Shape : Set where
  empty-shape unit-shape two-shape natural-shape : Shape
  product-shape sum-shape tree-shape identity-shape : Shape
  lifted-shape below-shape adjoined-shape : Shape

number : Shape → ℕ
number empty-shape = 0
number unit-shape = 1
number two-shape = 2
number natural-shape = 3
number product-shape = 4
number sum-shape = 5
number tree-shape = 6
number identity-shape = 7
number lifted-shape = 8
number below-shape = 9
number adjoined-shape = 10

-- The shape of a number, every number beyond the shapes the last.
shape-of : ℕ → Shape
shape-of 0 = empty-shape
shape-of 1 = unit-shape
shape-of 2 = two-shape
shape-of 3 = natural-shape
shape-of 4 = product-shape
shape-of 5 = sum-shape
shape-of 6 = tree-shape
shape-of 7 = identity-shape
shape-of 8 = lifted-shape
shape-of 9 = below-shape
shape-of (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))) =
  adjoined-shape

shape-of-number : (s : Shape) → shape-of (number s) ＝ s
shape-of-number empty-shape = refl
shape-of-number unit-shape = refl
shape-of-number two-shape = refl
shape-of-number natural-shape = refl
shape-of-number product-shape = refl
shape-of-number sum-shape = refl
shape-of-number tree-shape = refl
shape-of-number identity-shape = refl
shape-of-number lifted-shape = refl
shape-of-number below-shape = refl
shape-of-number adjoined-shape = refl

shape-is-set : is-set Shape
shape-is-set s = retract-unique number shape-of shape-of-number s
  (ℕ-is-set (number s))

------------------------------------------------------------------------
-- Names unfolded

module _ {ℓ : Level} (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ))
  (E : I → Set ℓ) where

  -- The fields of a name of each shape.
  Fields : Shape → Set (lsuc ℓ)
  Fields empty-shape = Lift (lsuc ℓ) 𝟙
  Fields unit-shape = Lift (lsuc ℓ) 𝟙
  Fields two-shape = Lift (lsuc ℓ) 𝟙
  Fields natural-shape = Lift (lsuc ℓ) 𝟙
  Fields product-shape =
    Σ (Name L D I E) (λ a → decode L D I E a → Name L D I E)
  Fields sum-shape =
    Σ (Name L D I E) (λ a → decode L D I E a → Name L D I E)
  Fields tree-shape =
    Σ (Name L D I E) (λ a → decode L D I E a → Name L D I E)
  Fields identity-shape =
    Σ (Name L D I E) (λ a → decode L D I E a × decode L D I E a)
  Fields lifted-shape = Lift (lsuc ℓ) L
  Fields below-shape = Lift (lsuc ℓ) 𝟙
  Fields adjoined-shape = I

module _ {ℓ : Level} {L : Set ℓ} {D : L → Set ℓ} {I : Set (lsuc ℓ)}
  {E : I → Set ℓ} where

  shape : Name L D I E → Shape
  shape (_ , emptyᶠ) = empty-shape
  shape (_ , unitᶠ) = unit-shape
  shape (_ , twoᶠ) = two-shape
  shape (_ , naturalᶠ) = natural-shape
  shape (_ , productᶠ fa fb) = product-shape
  shape (_ , sumᶠ fa fb) = sum-shape
  shape (_ , treeᶠ fa fb) = tree-shape
  shape (_ , identityᶠ fa x y) = identity-shape
  shape (_ , liftedᶠ l) = lifted-shape
  shape (_ , belowᶠ) = below-shape
  shape (_ , adjoinedᶠ i) = adjoined-shape

  -- The fields of a name: the names it is formed from, as names.
  fields : (u : Name L D I E) → Fields L D I E (shape u)
  fields (_ , emptyᶠ) = lift ⋆
  fields (_ , unitᶠ) = lift ⋆
  fields (_ , twoᶠ) = lift ⋆
  fields (_ , naturalᶠ) = lift ⋆
  fields (_ , productᶠ {A} {B} fa fb) = (A , fa) , (λ x → B x , fb x)
  fields (_ , sumᶠ {A} {B} fa fb) = (A , fa) , (λ x → B x , fb x)
  fields (_ , treeᶠ {A} {B} fa fb) = (A , fa) , (λ x → B x , fb x)
  fields (_ , identityᶠ {A} fa x y) = (A , fa) , (x , y)
  fields (_ , liftedᶠ l) = lift l
  fields (_ , belowᶠ) = lift ⋆
  fields (_ , adjoinedᶠ i) = i

  unfold : Name L D I E → Σ Shape (Fields L D I E)
  unfold u = shape u , fields u

  fold : Σ Shape (Fields L D I E) → Name L D I E
  fold (empty-shape , _) = empty
  fold (unit-shape , _) = unit
  fold (two-shape , _) = two
  fold (natural-shape , _) = natural
  fold (product-shape , (a , b)) = product a b
  fold (sum-shape , (a , b)) = sum a b
  fold (tree-shape , (a , b)) = tree a b
  fold (identity-shape , (a , (x , y))) = identity a x y
  fold (lifted-shape , lift l) = lifted l
  fold (below-shape , _) = below
  fold (adjoined-shape , i) = adjoined i

  fold-unfold : (u : Name L D I E) → fold (unfold u) ＝ u
  fold-unfold (_ , emptyᶠ) = refl
  fold-unfold (_ , unitᶠ) = refl
  fold-unfold (_ , twoᶠ) = refl
  fold-unfold (_ , naturalᶠ) = refl
  fold-unfold (_ , productᶠ fa fb) = refl
  fold-unfold (_ , sumᶠ fa fb) = refl
  fold-unfold (_ , treeᶠ fa fb) = refl
  fold-unfold (_ , identityᶠ fa x y) = refl
  fold-unfold (_ , liftedᶠ l) = refl
  fold-unfold (_ , belowᶠ) = refl
  fold-unfold (_ , adjoinedᶠ i) = refl

------------------------------------------------------------------------
-- Decodings and names are sets

module _ (ext : Extensionality) {ℓ : Level} {L : Set ℓ} {D : L → Set ℓ}
  {I : Set (lsuc ℓ)} {E : I → Set ℓ} (setL : is-set L)
  (setsD : (l : L) → is-set (D l)) (setI : is-set I)
  (setsE : (i : I) → is-set (E i)) where

  -- Mathematical shape: by recursion on the formation, each former of
  -- sets is a set.
  form-is-set : {X : Set ℓ} → Form L D I E X → is-set X
  form-is-set emptyᶠ =
    lifts-of-sets-are-sets ℓ (propositions-are-sets 𝟘-is-proposition)
  form-is-set unitᶠ =
    lifts-of-sets-are-sets ℓ (propositions-are-sets 𝟙-is-proposition)
  form-is-set twoᶠ = lifts-of-sets-are-sets ℓ 𝟚-is-set
  form-is-set naturalᶠ = lifts-of-sets-are-sets ℓ ℕ-is-set
  form-is-set (productᶠ fa fb) = Π-is-set ext (λ x → form-is-set (fb x))
  form-is-set (sumᶠ fa fb) =
    sums-of-sets-are-sets (form-is-set fa) (λ x → form-is-set (fb x))
  form-is-set (treeᶠ fa fb) = trees-over-a-set-are-sets
    (λ x → extensional ext) (λ x f g → extensional ext) (form-is-set fa)
  form-is-set (identityᶠ fa x y) =
    propositions-are-sets (form-is-set fa x y)
  form-is-set (liftedᶠ l) = setsD l
  form-is-set belowᶠ = setL
  form-is-set (adjoinedᶠ i) = setsE i

  decode-is-set : (a : Name L D I E) → is-set (decode L D I E a)
  decode-is-set (_ , f) = form-is-set f

  -- The identifications from a name are unique, through its fields, by
  -- recursion on the formation.
  form-unique :
    {X : Set ℓ} (f : Form L D I E X) → Unique {X = Name L D I E} (X , f)

  form-fields-unique : {X : Set ℓ} (f : Form L D I E X) →
    Unique (fields (X , f))

  form-unique {X} f = retract-unique unfold fold fold-unfold (X , f)
    (pair-unique (shape-is-set (shape (X , f))) (form-fields-unique f))

  form-fields-unique emptyᶠ =
    lifts-of-sets-are-sets (lsuc ℓ)
      (propositions-are-sets 𝟙-is-proposition) (lift ⋆)
  form-fields-unique unitᶠ =
    lifts-of-sets-are-sets (lsuc ℓ)
      (propositions-are-sets 𝟙-is-proposition) (lift ⋆)
  form-fields-unique twoᶠ =
    lifts-of-sets-are-sets (lsuc ℓ)
      (propositions-are-sets 𝟙-is-proposition) (lift ⋆)
  form-fields-unique naturalᶠ =
    lifts-of-sets-are-sets (lsuc ℓ)
      (propositions-are-sets 𝟙-is-proposition) (lift ⋆)
  form-fields-unique (productᶠ fa fb) = pair-unique (form-unique fa)
    (function-unique ext (λ x → form-unique (fb x)))
  form-fields-unique (sumᶠ fa fb) = pair-unique (form-unique fa)
    (function-unique ext (λ x → form-unique (fb x)))
  form-fields-unique (treeᶠ fa fb) = pair-unique (form-unique fa)
    (function-unique ext (λ x → form-unique (fb x)))
  form-fields-unique (identityᶠ fa x y) = pair-unique (form-unique fa)
    (sums-of-sets-are-sets (form-is-set fa) (λ _ → form-is-set fa) (x , y))
  form-fields-unique (liftedᶠ l) =
    lifts-of-sets-are-sets (lsuc ℓ) setL (lift l)
  form-fields-unique belowᶠ =
    lifts-of-sets-are-sets (lsuc ℓ)
      (propositions-are-sets 𝟙-is-proposition) (lift ⋆)
  form-fields-unique (adjoinedᶠ i) = setI i

  name-unique : (u : Name L D I E) → Unique u
  name-unique (_ , f) = form-unique f

  fields-unique : (u : Name L D I E) → Unique (fields u)
  fields-unique (_ , f) = form-fields-unique f

  name-is-set : is-set (Name L D I E)
  name-is-set = name-unique

