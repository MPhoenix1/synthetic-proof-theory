{-# OPTIONS --safe --without-K #-}

module SPT.IR.Layers where

-- A shape over a family as a layer over the outputs. The skeleton of a
-- shape reads its inputs as outputs (`skeleton`, `read`), and hypotheses
-- at its inputs collect at the skeleton's positions (`collect`). With
-- their outputs kept, shapes over W and layers with points of the fibers
-- of W's decoding at their inputs are one datum, under extensionality for
-- the arities (`Marked`, `Layered`): `up` is Action's assembly from the
-- identity family, `down` the skeleton with its canonical points, and they
-- are inverse (`up-down`, `down-up`, through the induction `layers`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Happly using
  (funext; funext-refl; homotopy-induction)

open import SPT.IR.Action using (shift; assemble)
open import SPT.IR.Description using
  (Desc; ι; σ; δ; Indexed; index; indexed; Shape; Mark)
open import SPT.IR.Restriction using
  (Position; input; Layer; points; points-η)

------------------------------------------------------------------------
-- Skeletons

-- The skeleton of a shape over Z replaces each recursive input by its
-- decoding, a shape over the identity family on the outputs; it has the
-- same output (`read`). Hypotheses at the inputs of the shape, in a family
-- Q over the outputs, are hypotheses at the positions of its skeleton.

module _
  {s κ j : Level} {E : Set j} (Z : Indexed κ E)
  where

  skeleton :
    (S : Desc {s = s} E) → Shape S Z → Shape S (indexed E (λ e → e))
  skeleton (ι x) z = lift ⋆
  skeleton (σ A H) (a , z) = a , skeleton (H a) z
  skeleton (δ A H) (f , z) =
    (λ x → index Z (f x)) , skeleton (H (λ x → index Z (f x))) z

  read :
    (S : Desc {s = s} E) (z : Shape S Z)
    → Mark S (indexed E (λ e → e)) (skeleton S z) ＝ Mark S Z z
  read (ι x) z = refl
  read (σ A H) (a , z) = read (H a) z
  read (δ A H) (f , z) = read (H (λ x → index Z (f x))) z

  collect :
    {q : Level} (Q : E → Set q) (S : Desc {s = s} E) (z : Shape S Z)
    → ((p : Position S Z z) → Q (index Z (input S Z z p)))
    → (p : Position S (indexed E (λ e → e)) (skeleton S z))
    → Q (input S (indexed E (λ e → e)) (skeleton S z) p)
  collect Q (ι x) z h (lift ())
  collect Q (σ A H) (a , z) h p = collect Q (H a) z h p
  collect Q (δ A H) (f , z) h p =
    points (λ e → e) Q A H (λ x → index Z (f x))
      (skeleton (H (λ x → index Z (f x))) z)
      (λ x → h (inl x))
      (collect Q (H (λ x → index Z (f x))) z (λ r → h (inr r)))
      p

  -- Collection commutes with a map of the hypotheses.

  collect-natural :
    {q r : Level} (Q : E → Set q) (R : E → Set r)
    (g : (e : E) → Q e → R e) (S : Desc {s = s} E) (z : Shape S Z)
    (h : (p : Position S Z z) → Q (index Z (input S Z z p)))
    (p : Position S (indexed E (λ e → e)) (skeleton S z))
    → collect R S z (λ t → g (index Z (input S Z z t)) (h t)) p
      ＝ g (input S (indexed E (λ e → e)) (skeleton S z) p)
          (collect Q S z h p)
  collect-natural Q R g (ι x) z h (lift ())
  collect-natural Q R g (σ A H) (a , z) h p =
    collect-natural Q R g (H a) z h p
  collect-natural Q R g (δ A H) (f , z) h (inl x) = refl
  collect-natural Q R g (δ A H) (f , z) h (inr p) =
    collect-natural Q R g (H (λ x → index Z (f x))) z (λ t → h (inr t)) p

------------------------------------------------------------------------
-- Shapes and layers with their outputs

-- A shape over W with an identification of its output, and a layer over
-- the outputs with points of the fibers of W's decoding at its inputs and
-- an identification of the output of its shape.

Marked :
  {s κ j : Level} {E : Set j} (S : Desc {s = s} E) (W : Indexed κ E) → E
  → Set (s ⊔ κ ⊔ j)
Marked S W o = Σ (Shape S W) (λ y → Mark S W y ＝ o)

Layered :
  {s κ j : Level} {E : Set j} (S : Desc {s = s} E) (W : Indexed κ E) → E
  → Set (s ⊔ κ ⊔ j)
Layered {E = E} S W o =
  Σ (Layer (λ e → e) (fiber (index W)) S)
    (λ l → Mark S (indexed E (λ e → e)) (pr₁ l) ＝ o)

-- Extensionality for assignments, adjusted to send the constant homotopy
-- to refl (SPT.Foundation.Happly).

normal :
  {s j : Level} (E : Set j)
  → ((A : Set s) (B : A → Set j) → FunExt A B)
  → (A : Set s) → FunExt A (λ _ → E)
normal E arities A = funext (arities A (λ _ → E))

------------------------------------------------------------------------
-- From layers to shapes and back

-- `up` assembles a layer from the identity family; `down` takes the
-- skeleton of a shape with the canonical point at each input.

module _
  {s κ j : Level} {E : Set j}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B) (W : Indexed κ E)
  where

  up : (S : Desc {s = s} E) (o : E) → Layered S W o → Marked S W o
  up S o ((c , h) , m) =
    let a = assemble (normal E arities) (indexed E (λ e → e)) W S c h
    in pr₁ a , (pr₂ a ∙ m)

module _
  {s κ j : Level} {E : Set j} (W : Indexed κ E)
  where

  canonical :
    (S : Desc {s = s} E) (y : Shape S W) (p : Position S W y)
    → fiber (index W) (index W (input S W y p))
  canonical S y p = input S W y p , refl

  down : (S : Desc {s = s} E) (o : E) → Marked S W o → Layered S W o
  down S o (y , m) =
    ( skeleton W S y
    , collect W (fiber (index W)) S y (canonical S y))
    , (read W S y ∙ m)

------------------------------------------------------------------------
-- Assembling a shape is assembling its skeleton

-- Action's assembly from any family is the assembly of the skeleton with
-- the collected points, clause by clause: at a δ the two read the same
-- identification of assignments.

module _
  {s κ κ′ j : Level} {E : Set j}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (Z : Indexed κ E) (W : Indexed κ′ E)
  where

  assembled :
    (S : Desc {s = s} E) (z : Shape S Z)
    (h : (p : Position S Z z) → fiber (index W) (index Z (input S Z z p)))
    → assemble (normal E arities) Z W S z h
      ＝ up arities W S (Mark S Z z)
          ( (skeleton Z S z , collect Z (fiber (index W)) S z h)
          , read Z S z)
  assembled (ι x) z h = refl
  assembled (σ A H) (a , z) h =
    ap (λ r → (a , pr₁ r) , pr₂ r) (assembled (H a) z h)
  assembled (δ A H) (f , z) h =
    let d =
          normal E arities A
            (λ x → index W (pr₁ (h (inl x))))
            (λ x → index Z (f x))
            (λ x → pr₂ (h (inl x)))
        r =
          assemble (normal E arities) (indexed E (λ e → e)) W
            (H (λ x → index Z (f x)))
            (skeleton Z (H (λ x → index Z (f x))) z)
            (collect Z (fiber (index W)) (H (λ x → index Z (f x))) z
              (λ p → h (inr p)))
    in
    ap
      (λ t →
        ((λ x → pr₁ (h (inl x))) , pr₁ (shift W H d (pr₁ t)))
        , (pr₂ (shift W H d (pr₁ t)) ∙ pr₂ t))
      (assembled (H (λ x → index Z (f x))) z (λ p → h (inr p)))
    ∙ ap
        (λ w →
          ((λ x → pr₁ (h (inl x))) , pr₁ (shift W H d (pr₁ r))) , w)
        (∙assoc (pr₂ (shift W H d (pr₁ r))) (pr₂ r)
          (read Z (H (λ x → index Z (f x))) z)
          ⁻¹)

------------------------------------------------------------------------
-- The two inverse laws

-- Assembling a shape at its canonical points returns it: extensionality
-- is normal, so the identification at a δ is refl. Every layer is `down`
-- of a shape: at a δ the points are a code with an identification from its
-- decoding, and homotopy induction reduces to the constant identification.

module _
  {s κ j : Level} {E : Set j}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B) (W : Indexed κ E)
  where

  assemble-canonical :
    (S : Desc {s = s} E) (y : Shape S W)
    → assemble (normal E arities) W W S y (canonical W S y) ＝ (y , refl)
  assemble-canonical (ι x) y = refl
  assemble-canonical (σ A H) (a , y) =
    ap (λ r → (a , pr₁ r) , pr₂ r) (assemble-canonical (H a) y)
  assemble-canonical (δ A H) (f , y) =
    ap₂
      (λ d r →
        (f , pr₁ (shift W H d (pr₁ r)))
        , (pr₂ (shift W H d (pr₁ r)) ∙ pr₂ r))
      (funext-refl (arities A (λ _ → E)) (λ x → index W (f x)))
      (assemble-canonical (H (λ x → index W (f x))) y)

  up-down :
    (S : Desc {s = s} E) (o : E) (a : Marked S W o)
    → up arities W S o (down W S o a) ＝ a
  up-down S o (y , m) =
    let a =
          assemble (normal E arities) (indexed E (λ e → e)) W S
            (skeleton W S y)
            (collect W (fiber (index W)) S y (canonical W S y))
    in
    ap (λ w → pr₁ a , w) (∙assoc (pr₂ a) (read W S y) m ⁻¹)
    ∙ ap (λ r → pr₁ r , (pr₂ r ∙ m))
        ( assembled arities W W S y (canonical W S y) ⁻¹
        ∙ assemble-canonical S y)

module _
  {s κ j : Level} {E : Set j}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions : (A : Set s) (B : A → Set (κ ⊔ j)) → FunExt A B)
  (W : Indexed κ E)
  where

  layers :
    {μ : Level} (S : Desc {s = s} E) (o : E) (P : Layered S W o → Set μ)
    → ((a : Marked S W o) → P (down W S o a))
    → (l : Layered S W o) → P l
  layers (ι x) o P step ((lift ⋆ , h) , m) =
    transport (λ k → P ((lift ⋆ , k) , m))
      ( positions (Lift s 𝟘)
          (λ p →
            fiber (index W)
              (input (ι x) (indexed E (λ e → e)) (lift ⋆) p))
          (collect W (fiber (index W)) (ι x) (lift ⋆)
            (canonical W (ι x) (lift ⋆)))
          h
          (λ p → 𝟘-elim (lower p)))
      (step (lift ⋆ , m))
  layers (σ A H) o P step (((a , c) , h) , m) =
    layers (H a) o
      (λ l → P (((a , pr₁ (pr₁ l)) , pr₂ (pr₁ l)) , pr₂ l))
      (λ b → step ((a , pr₁ b) , pr₂ b))
      ((c , h) , m)
  layers (δ A H) o P step (((q , c) , h) , m) =
    let w = λ (x : A) → pr₁ (h (inl x))
    in
    transport (λ k → P (((q , c) , k) , m))
      ( positions (Position (δ A H) (indexed E (λ e → e)) (q , c))
          (λ p →
            fiber (index W)
              (input (δ A H) (indexed E (λ e → e)) (q , c) p))
          ( points (λ e → e) (fiber (index W)) A H q c
              (λ x → h (inl x)) (λ r → h (inr r)))
          h
          (points-η (λ e → e) (fiber (index W)) A H q c h))
      ( homotopy-induction (λ x → index W (w x))
          (arities A (λ x → Σ E (λ y → index W (w x) ＝ y)))
          ( λ r d →
              (c′ : Shape (H r) (indexed E (λ e → e)))
              (h′ :
                (p : Position (H r) (indexed E (λ e → e)) c′)
                → fiber (index W) (input (H r) (indexed E (λ e → e)) c′ p))
              (m′ : Mark (H r) (indexed E (λ e → e)) c′ ＝ o)
              → P ( ( (r , c′)
                    , points (λ e → e) (fiber (index W)) A H r c′
                        (λ x → w x , d x) h′)
                  , m′))
          ( λ c′ h′ m′ →
              layers (H (λ x → index W (w x))) o
                ( λ l →
                    P ( ( ((λ x → index W (w x)) , pr₁ (pr₁ l))
                        , points (λ e → e) (fiber (index W)) A H
                            (λ x → index W (w x)) (pr₁ (pr₁ l))
                            (λ x → w x , refl) (pr₂ (pr₁ l)))
                      , pr₂ l))
                (λ b → step ((w , pr₁ b) , pr₂ b))
                ((c′ , h′) , m′))
          q
          (λ x → pr₂ (h (inl x)))
          c (λ r → h (inr r)) m)

  down-up :
    (S : Desc {s = s} E) (o : E) (l : Layered S W o)
    → down W S o (up arities W S o l) ＝ l
  down-up S o =
    layers S o
      (λ l → down W S o (up arities W S o l) ＝ l)
      (λ a → ap (down W S o) (up-down arities W S o a))
