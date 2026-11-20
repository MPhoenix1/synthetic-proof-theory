{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Comparison where

-- Residence up to isomorphism. For a small family whose names form a set,
-- the carrier of any least closure is isomorphic to the generated total
-- (resides): a code goes to the generated member it codes (coded, from
-- Presentation's members), a generated member to the code naming it
-- (naming, from Presentation's name-in), and the two returns hold by the
-- closure's induction (recovers) and by recursion on the witnesses
-- (returns). So absorption gives, for every operator, a name whose decoding
-- is isomorphic to the generated total (absorption-resides), and literal
-- residence wherever isomorphic types of level ℓ are identified
-- (residence). Function extensionality at one level joins the branches.
-- That the names form a set identifies the paths between names that the two
-- returns produce; it is used nowhere else.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Isomorphisms using (_≅_)
open import SPT.Foundation.Propositions using (is-set)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; map; Name; Closure; Reflection)
open import SPT.Mahlo.Residence.Absorption using
  (Methods; Induction; Absorbed; Absorption)
open import SPT.Mahlo.Residence.Membership using
  ( Form; emptyᶠ; unitᶠ; twoᶠ; naturalᶠ; productᶠ; sumᶠ; treeᶠ
  ; identityᶠ; resultᶠ; branchᶠ; generated; Residence
  )
open import SPT.Mahlo.Residence.Names using
  (branch-along; realized-family; identity-name)
open import SPT.Mahlo.Residence.Presentation using
  (member-methods; members; name-in)

------------------------------------------------------------------------
-- Identifications of families, and transport between names

-- Families agree when their heads agree and their branches agree along
-- the identification of the heads.
family-path :
    {ℓ : Level} {T : Set ℓ}
    (E : T → Set ℓ)
    (extensionality : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
    {t t′ : T} {f : E t → T} {f′ : E t′ → T}
    (H : t ＝ t′)
  → ((y : E t) → f y ＝ f′ (transport E H y))
  → _＝_ {A = Σ T (λ s → E s → T)} (t , f) (t′ , f′)
family-path {T = T} E extensionality {t} {f = f} {f′ = f′} refl fs =
  ap (λ k → t , k) (extensionality (E t) (λ _ → T) f f′ fs)

module _
  {κ ℓ : Level} {C : Set κ}
  (D : C → Set ℓ)
  (names : is-set C)
  where

  -- Parallel identifications of names transport alike.
  parallel :
      {c c′ : C}
      (p q : c ＝ c′)
      (u : D c)
    → transport D p u ＝ transport D q u
  parallel {c} {c′} p q u = ap (λ r → transport D r u) (names c c′ p q)

  -- Transport around a cycle of names returns.
  cycle :
      {c c₁ c₂ : C}
      (p : c ＝ c₁)
      (q : c₁ ＝ c₂)
      (r : c₂ ＝ c)
      (u : D c)
    → transport D r (transport D q (transport D p u)) ＝ u
  cycle refl refl r u = parallel r refl u

------------------------------------------------------------------------
-- Generated members of codes, and codes of generated members

module _
  {ℓ : Level} {C : Set ℓ} {D : C → Set ℓ}
  (Q : Formers C D) (Ψ : Operator D)
  (names : is-set C)
  (extensionality : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
  where

  -- The generated member coded by a code of a least closure.
  coded :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
    → Induction L ℓ
    → A
    → Σ C (Form Q Ψ)
  coded L ind a = Closure.interpret L a , members Q Ψ L ind a

  -- The code naming a generated member.
  naming :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
    → Σ C (Form Q Ψ)
    → A
  naming L w =
    pr₁ (name-in Q Ψ (λ (X : Set ℓ) → extensionality X (λ _ → C)) L (pr₂ w))

  -- A code whose member is a witness moved along its naming equation
  -- codes that witness.
  landing :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      (ind : Induction L ℓ)
      (a : A)
      {c : C}
      (e : Closure.interpret L a ＝ c)
      {w : Form Q Ψ c}
    → members Q Ψ L ind a ＝ transport (Form Q Ψ) (e ⁻¹) w
    → coded L ind a ＝ (c , w)
  landing L ind a refl p =
    ap (λ v → Closure.interpret L a , v) p

  -- The second components of an identification of generated members.
  fiberwise :
      {s t : Σ C (Form Q Ψ)}
      (P : s ＝ t)
    → transport (Form Q Ψ) (ap pr₁ P) (pr₂ s) ＝ pr₂ t
  fiberwise refl = refl

  -- Generated members over one name agree when their pairs do.
  settled :
      {c : C}
      {v w : Form Q Ψ c}
    → _＝_ {A = Σ C (Form Q Ψ)} (c , v) (c , w)
    → v ＝ w
  settled {c} {v} P =
    parallel (Form Q Ψ) names (ap pr₁ P) refl v ⁻¹ ∙ fiberwise P

  -- The branches of the inner family at identified families agree at
  -- transported points.
  inner-shift :
      {B : Set ℓ}
      (M : Closure Q Ψ B)
      {F F′ : Family (Decode D (Closure.interpret M))}
      (K : F ＝ F′)
      (u : Decode D (Closure.interpret M) (pr₁ (Closure.inner M F)))
    → pr₂ (Closure.inner M F) u
      ＝ pr₂ (Closure.inner M F′)
          ( transport
              ( λ G →
                  Decode D (Closure.interpret M) (pr₁ (Closure.inner M G)))
              K
              u)
  inner-shift M refl u = refl

------------------------------------------------------------------------
-- Generated members return

-- A family of generated members whose head and branches are named
-- returns, through their codes, to itself.

  joined :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      (ind : Induction L ℓ)
      (Y : Family (λ (w : Σ C (Form Q Ψ)) → D (pr₁ w)))
      (head : Name (Closure.interpret L) (pr₁ (pr₁ Y)))
      (branches :
          (z : D (pr₁ (pr₁ Y)))
        → Name (Closure.interpret L) (pr₁ (pr₂ Y z)))
    → coded L ind (pr₁ head) ＝ pr₁ Y
    → ((z : D (pr₁ (pr₁ Y)))
      → coded L ind (pr₁ (branches z)) ＝ pr₂ Y z)
    → _＝_ {A = Family (λ (w : Σ C (Form Q Ψ)) → D (pr₁ w))}
        ( coded L ind (pr₁ head)
        , (λ y → coded L ind (pr₁ (branches (transport D (pr₂ head) y)))))
        Y
  joined L ind Y head branches back backs =
    family-path (λ w → D (pr₁ w)) extensionality back
      ( λ y →
          backs (transport D (pr₂ head) y)
          ∙ ap (pr₂ Y)
              ( parallel D names (pr₂ head) (ap pr₁ back) y
                ∙ transport-ap D pr₁ back y ⁻¹))

  identity-return :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      (ind : Induction L ℓ)
      (a : Σ C (Form Q Ψ))
      (n : Name (Closure.interpret L) (pr₁ a))
    → coded L ind (pr₁ n) ＝ a
    → (x y : D (pr₁ a))
    → coded L ind (pr₁ (identity-name Q Ψ L n x y))
      ＝ (Formers.identity Q (pr₁ a) x y , identityᶠ a x y)
  identity-return L ind (c , v) (b , refl) back x y =
    landing L ind (pr₁ (Closure.identity L b x y))
      ( pr₂ (Closure.identity L b x y))
      ( Induction.induction-identity ind
          ( λ a → Form Q Ψ (Closure.interpret L a))
          ( member-methods Q Ψ L) b x y)
    ∙ ap
        ( λ u →
            Formers.identity Q (Closure.interpret L b) x y
            , identityᶠ (Closure.interpret L b , u) x y)
        ( settled back)

  returns :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      (ind : Induction L ℓ)
      {c : C}
      (w : Form Q Ψ c)
    → coded L ind (naming L (c , w)) ＝ (c , w)
  returns L ind emptyᶠ =
    landing L ind (pr₁ (Closure.empty L)) (pr₂ (Closure.empty L))
      ( Induction.induction-empty ind
          ( λ a → Form Q Ψ (Closure.interpret L a)) (member-methods Q Ψ L))
  returns L ind unitᶠ =
    landing L ind (pr₁ (Closure.unit L)) (pr₂ (Closure.unit L))
      ( Induction.induction-unit ind
          ( λ a → Form Q Ψ (Closure.interpret L a)) (member-methods Q Ψ L))
  returns L ind twoᶠ =
    landing L ind (pr₁ (Closure.two L)) (pr₂ (Closure.two L))
      ( Induction.induction-two ind
          ( λ a → Form Q Ψ (Closure.interpret L a)) (member-methods Q Ψ L))
  returns L ind naturalᶠ =
    landing L ind (pr₁ (Closure.natural L))
      ( pr₂ (Closure.natural L))
      ( Induction.induction-natural ind
          ( λ a → Form Q Ψ (Closure.interpret L a)) (member-methods Q Ψ L))
  returns L ind (productᶠ Y) =
    let e = λ (X : Set ℓ) → extensionality X (λ _ → C)
        R = realized-family Q Ψ e L (λ z → pr₁ (pr₂ Y z))
              ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
              ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
    in
    landing L ind (pr₁ (Closure.product L (pr₁ R)))
      ( pr₂ (Closure.product L (pr₁ R)))
      ( Induction.induction-product ind
          ( λ a → Form Q Ψ (Closure.interpret L a))
          ( member-methods Q Ψ L) (pr₁ R))
    ∙ ap (λ Z → pr₁ (Closure.product (generated Q Ψ) Z))
        ( joined L ind Y
            ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
            ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
            ( returns L ind (pr₂ (pr₁ Y)))
            ( λ z → returns L ind (pr₂ (pr₂ Y z))))
  returns L ind (sumᶠ Y) =
    let e = λ (X : Set ℓ) → extensionality X (λ _ → C)
        R = realized-family Q Ψ e L (λ z → pr₁ (pr₂ Y z))
              ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
              ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
    in
    landing L ind (pr₁ (Closure.sum L (pr₁ R)))
      ( pr₂ (Closure.sum L (pr₁ R)))
      ( Induction.induction-sum ind
          ( λ a → Form Q Ψ (Closure.interpret L a))
          ( member-methods Q Ψ L) (pr₁ R))
    ∙ ap (λ Z → pr₁ (Closure.sum (generated Q Ψ) Z))
        ( joined L ind Y
            ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
            ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
            ( returns L ind (pr₂ (pr₁ Y)))
            ( λ z → returns L ind (pr₂ (pr₂ Y z))))
  returns L ind (treeᶠ Y) =
    let e = λ (X : Set ℓ) → extensionality X (λ _ → C)
        R = realized-family Q Ψ e L (λ z → pr₁ (pr₂ Y z))
              ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
              ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
    in
    landing L ind (pr₁ (Closure.tree L (pr₁ R)))
      ( pr₂ (Closure.tree L (pr₁ R)))
      ( Induction.induction-tree ind
          ( λ a → Form Q Ψ (Closure.interpret L a))
          ( member-methods Q Ψ L) (pr₁ R))
    ∙ ap (λ Z → pr₁ (Closure.tree (generated Q Ψ) Z))
        ( joined L ind Y
            ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
            ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
            ( returns L ind (pr₂ (pr₁ Y)))
            ( λ z → returns L ind (pr₂ (pr₂ Y z))))
  returns L ind (identityᶠ a x y) =
    identity-return L ind a
      ( name-in Q Ψ (λ (X : Set ℓ) → extensionality X (λ _ → C)) L (pr₂ a))
      ( returns L ind (pr₂ a))
      x
      y
  returns L ind (resultᶠ Y) =
    let e = λ (X : Set ℓ) → extensionality X (λ _ → C)
        R = realized-family Q Ψ e L (λ z → pr₁ (pr₂ Y z))
              ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
              ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
    in
    landing L ind (pr₁ (Closure.inner L (pr₁ R)))
      ( ap pr₁ (Closure.inner-β L (pr₁ R)))
      ( Induction.induction-result ind
          ( λ a → Form Q Ψ (Closure.interpret L a))
          ( member-methods Q Ψ L) (pr₁ R))
    ∙ ap (λ Z → pr₁ (Closure.inner (generated Q Ψ) Z))
        ( joined L ind Y
            ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
            ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
            ( returns L ind (pr₂ (pr₁ Y)))
            ( λ z → returns L ind (pr₂ (pr₂ Y z))))
  returns L ind (branchᶠ Y y) =
    let e = λ (X : Set ℓ) → extensionality X (λ _ → C)
        R = realized-family Q Ψ e L (λ z → pr₁ (pr₂ Y z))
              ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
              ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
        K = joined L ind Y
              ( name-in Q Ψ e L (pr₂ (pr₁ Y)))
              ( λ z → name-in Q Ψ e L (pr₂ (pr₂ Y z)))
              ( returns L ind (pr₂ (pr₁ Y)))
              ( λ z → returns L ind (pr₂ (pr₂ Y z)))
        p = ap pr₁ (Closure.inner-β L (pr₁ R) ∙ ap Ψ (pr₂ R)) ⁻¹
        q = ap pr₁ (Closure.inner-β L (pr₁ R))
    in
    landing L ind
      ( pr₂ (Closure.inner L (pr₁ R)) (transport D p y))
      ( branch-along D (Closure.inner-β L (pr₁ R)) (transport D p y))
      ( Induction.induction-branch ind
          ( λ a → Form Q Ψ (Closure.interpret L a))
          ( member-methods Q Ψ L) (pr₁ R) (transport D p y))
    ∙ ( inner-shift (generated Q Ψ) K (transport D q (transport D p y))
      ∙ ap (pr₂ (Closure.inner (generated Q Ψ) Y))
          ( transport-ap D
              ( λ G →
                  pr₁ (Ψ (map D (Closure.interpret (generated Q Ψ)) G)))
              K
              ( transport D q (transport D p y))
          ∙ cycle D names p q
              ( ap
                  ( λ G →
                      pr₁ (Ψ (map D (Closure.interpret (generated Q Ψ)) G)))
                  K)
              y))

------------------------------------------------------------------------
-- Codes return

-- A family of codes whose head and branches are named by codes equal to
-- them is named by itself.

  rejoined :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      (φ : Family (Decode D (Closure.interpret L)))
      (head : Name (Closure.interpret L) (Closure.interpret L (pr₁ φ)))
      (branches :
          (z : Decode D (Closure.interpret L) (pr₁ φ))
        → Name (Closure.interpret L) (Closure.interpret L (pr₂ φ z)))
    → pr₁ head ＝ pr₁ φ
    → ((z : Decode D (Closure.interpret L) (pr₁ φ))
      → pr₁ (branches z) ＝ pr₂ φ z)
    → _＝_ {A = Family (Decode D (Closure.interpret L))}
        ( pr₁ head , (λ y → pr₁ (branches (transport D (pr₂ head) y))))
        φ
  rejoined L φ head branches back backs =
    family-path (Decode D (Closure.interpret L)) extensionality back
      ( λ y →
          backs (transport D (pr₂ head) y)
          ∙ ap (pr₂ φ)
              ( parallel D names (pr₂ head)
                  ( ap (Closure.interpret L) back) y
                ∙ transport-ap D (Closure.interpret L) back y ⁻¹))

  -- A name of a code's own name by a code equal to it is the code itself.
  named-at :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      (a : A)
      (n : Name (Closure.interpret L) (Closure.interpret L a))
    → pr₁ n ＝ a
    → n ＝ (a , refl)
  named-at L a (b , e) refl =
    ap (λ r → a , r)
      ( names (Closure.interpret L a) (Closure.interpret L a) e refl)

  recover-methods :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      (ind : Induction L ℓ)
    → Methods L (λ a → naming L (coded L ind a) ＝ a)
  recover-methods L ind =
    let e = λ (X : Set ℓ) → extensionality X (λ _ → C)
    in record
    { on-empty = ap (naming L) (returns L ind emptyᶠ)
    ; on-unit = ap (naming L) (returns L ind unitᶠ)
    ; on-two = ap (naming L) (returns L ind twoᶠ)
    ; on-natural = ap (naming L) (returns L ind naturalᶠ)
    ; on-product = λ φ back backs →
        ap (naming L)
          ( landing L ind (pr₁ (Closure.product L φ))
              ( pr₂ (Closure.product L φ))
              ( Induction.induction-product ind
                  ( λ a → Form Q Ψ (Closure.interpret L a))
                  ( member-methods Q Ψ L) φ))
        ∙ ap (λ F → pr₁ (Closure.product L F))
            ( rejoined L φ
                ( name-in Q Ψ e L (members Q Ψ L ind (pr₁ φ)))
                ( λ z → name-in Q Ψ e L (members Q Ψ L ind (pr₂ φ z)))
                back backs)
    ; on-sum = λ φ back backs →
        ap (naming L)
          ( landing L ind (pr₁ (Closure.sum L φ))
              ( pr₂ (Closure.sum L φ))
              ( Induction.induction-sum ind
                  ( λ a → Form Q Ψ (Closure.interpret L a))
                  ( member-methods Q Ψ L) φ))
        ∙ ap (λ F → pr₁ (Closure.sum L F))
            ( rejoined L φ
                ( name-in Q Ψ e L (members Q Ψ L ind (pr₁ φ)))
                ( λ z → name-in Q Ψ e L (members Q Ψ L ind (pr₂ φ z)))
                back backs)
    ; on-tree = λ φ back backs →
        ap (naming L)
          ( landing L ind (pr₁ (Closure.tree L φ))
              ( pr₂ (Closure.tree L φ))
              ( Induction.induction-tree ind
                  ( λ a → Form Q Ψ (Closure.interpret L a))
                  ( member-methods Q Ψ L) φ))
        ∙ ap (λ F → pr₁ (Closure.tree L F))
            ( rejoined L φ
                ( name-in Q Ψ e L (members Q Ψ L ind (pr₁ φ)))
                ( λ z → name-in Q Ψ e L (members Q Ψ L ind (pr₂ φ z)))
                back backs)
    ; on-identity = λ a x y back →
        ap (naming L)
          ( landing L ind (pr₁ (Closure.identity L a x y))
              ( pr₂ (Closure.identity L a x y))
              ( Induction.induction-identity ind
                  ( λ b → Form Q Ψ (Closure.interpret L b))
                  ( member-methods Q Ψ L) a x y))
        ∙ ap (λ n → pr₁ (identity-name Q Ψ L n x y))
            ( named-at L a
                ( name-in Q Ψ e L (members Q Ψ L ind a))
                back)
    ; on-result = λ φ back backs →
        ap (naming L)
          ( landing L ind (pr₁ (Closure.inner L φ))
              ( ap pr₁ (Closure.inner-β L φ))
              ( Induction.induction-result ind
                  ( λ a → Form Q Ψ (Closure.interpret L a))
                  ( member-methods Q Ψ L) φ))
        ∙ ap (λ F → pr₁ (Closure.inner L F))
            ( rejoined L φ
                ( name-in Q Ψ e L (members Q Ψ L ind (pr₁ φ)))
                ( λ z → name-in Q Ψ e L (members Q Ψ L ind (pr₂ φ z)))
                back backs)
    ; on-branch = λ φ y back backs →
        let R = realized-family Q Ψ e L
                  ( λ z → Closure.interpret L (pr₂ φ z))
                  ( name-in Q Ψ e L (members Q Ψ L ind (pr₁ φ)))
                  ( λ z → name-in Q Ψ e L (members Q Ψ L ind (pr₂ φ z)))
            K = rejoined L φ
                  ( name-in Q Ψ e L (members Q Ψ L ind (pr₁ φ)))
                  ( λ z → name-in Q Ψ e L (members Q Ψ L ind (pr₂ φ z)))
                  back backs
            p = ap pr₁ (Closure.inner-β L φ)
            q = ap pr₁ (Closure.inner-β L (pr₁ R) ∙ ap Ψ (pr₂ R)) ⁻¹
        in
        ap (naming L)
          ( landing L ind (pr₂ (Closure.inner L φ) y)
              ( branch-along D (Closure.inner-β L φ) y)
              ( Induction.induction-branch ind
                  ( λ a → Form Q Ψ (Closure.interpret L a))
                  ( member-methods Q Ψ L) φ y))
        ∙ ( inner-shift L K (transport D q (transport D p y))
          ∙ ap (pr₂ (Closure.inner L φ))
              ( transport-ap D
                  ( λ G → Closure.interpret L (pr₁ (Closure.inner L G)))
                  K
                  ( transport D q (transport D p y))
              ∙ cycle D names p q
                  ( ap
                      ( λ G → Closure.interpret L (pr₁ (Closure.inner L G)))
                      K)
                  y))
    }

  recovers :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
      (ind : Induction L ℓ)
      (a : A)
    → naming L (coded L ind a) ＝ a
  recovers L ind =
    Induction.induction ind (λ a → naming L (coded L ind a) ＝ a)
      ( recover-methods L ind)

------------------------------------------------------------------------
-- Residence up to isomorphism

  resides :
      {A : Set ℓ}
      (L : Closure Q Ψ A)
    → Induction L ℓ
    → A ≅ Σ C (Form Q Ψ)
  resides L ind = record
    { forward = coded L ind
    ; backward = naming L
    ; backward-forward = recovers L ind
    ; forward-backward = λ w → returns L ind (pr₂ w)
    }

  absorbed-resides :
      Absorbed Q Ψ ℓ
    → Σ C (λ c → D c ≅ Σ C (Form Q Ψ))
  absorbed-resides absorbed =
    Reflection.carrier (Absorbed.reflection absorbed)
    , resides (Reflection.closure (Absorbed.reflection absorbed))
        ( Absorbed.induction absorbed)

module _
  {ℓ : Level} {C : Set ℓ} {D : C → Set ℓ}
  (Q : Formers C D)
  (names : is-set C)
  (extensionality : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
  where

  absorption-resides :
      Absorption Q ℓ
    → (Ψ : Operator D)
    → Σ C (λ c → D c ≅ Σ C (Form Q Ψ))
  absorption-resides absorption Ψ =
    absorbed-resides Q Ψ names extensionality (Absorption.absorb absorption Ψ)

  -- Mathematical shape: (Π X Y. X ≅ Y → X = Y) ⇒ Absorption ⇒ Residence.
  residence :
      ((X Y : Set ℓ) → X ≅ Y → X ＝ Y)
    → Absorption Q ℓ
    → Residence Q
  residence identify absorption Ψ =
    pr₁ (absorption-resides absorption Ψ)
    , identify (D (pr₁ (absorption-resides absorption Ψ)))
        ( Σ C (Form Q Ψ))
        ( pr₂ (absorption-resides absorption Ψ))
