{-# OPTIONS --safe --without-K --no-projection-like #-}

module SPT.MartinLof.Soundness.WellFounded.Method where

-- The context and the type of W-induction's method, read at arbitrary
-- environments. The method lives over a shape x : A, children
-- f : B x → W A B and hypotheses h : (y : B x) → M (f y)
-- (Rules.WellFounded's `method-context`), and has type M (sup x f)
-- (`method-type`). Read at environments whose first entries are the
-- values of x, f and h, these types are the model's at those values:
--
--   children     (B x → W A B)            at x ∷ E      (`children-value`)
--   hypotheses   ((y : B x) → M (f y))    at f ∷ x ∷ E  (`hypotheses-value`)
--   method type  M (sup x f)              at h ∷ f ∷ x ∷ E
--                                                       (`method-type-value`)
--
-- with M read at the extension by B x, at the application of f to the
-- new variable. The application f y and sup x f are stable there by the
-- soundness of Π (`application-stable`) and of sup (`supremum-stable`),
-- as the substitution lemma asks.

open import SPT.Base hiding (Lift; _∘_; id; lift; lower; zero)
open import SPT.Foundation.Vectors.Tabulation using (tabulate-lookup)
import SPT.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Binding as Binding
import SPT.MartinLof.Formers as Formers
import SPT.MartinLof.Raw as Raw
import SPT.MartinLof.Rules.WellFounded as Block
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell; Code; code-[])
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using (WellFounded)
import SPT.MartinLof.Soundness.Environment as Environment
import SPT.MartinLof.Soundness.Instances as Instances
import SPT.MartinLof.Soundness.Interpretation as Interpretation
import SPT.MartinLof.Soundness.Pi as Products
import SPT.MartinLof.Soundness.Transport as Transport
import SPT.MartinLof.Soundness.Typing as Typing
import SPT.MartinLof.Soundness.WellFounded.Trees as Trees

module _ {ℓ : Level} {C : Set}
  (R : Russell ℓ) (let open Russell R)
  (lifting : Lift R) (let open Lift lifting)
  (products : Pi R) (let open Pi products)
  (pairs : Sigma R) (let open Sigma pairs)
  (paths : Identity R) (let open Identity paths)
  (trees : WellFounded R products) (let open WellFounded trees)
  (nothing : Empty R) (let open Empty nothing)
  (one : Unit R) (let open Unit one)
  (sums : Sum R) (let open Sum sums)
  (numbers : Natural R) (let open Natural numbers)
  (operations : Operations R) (let open Operations operations)
  (subuniverses : Subuniverse R products operations)
  (constant : C → Tm ◇)
  (let ext = Environment.ext R)
  (let _[_]ᵉ = Environment._[_]ᵉ R)
  (let Stable = Environment.Stable R)
  (let meaning = Interpretation.⟦_⟧ R lifting products pairs paths trees
                   nothing one sums numbers operations subuniverses constant)
  (let bound-meaning = Transport.bound-meaning R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let weaken-stable = Instances.weaken-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let rename-value = Instances.rename-value R lifting products pairs paths
                        trees nothing one sums numbers operations subuniverses
                          constant)
  (let instantiate-past-value = Instances.instantiate-past-value R lifting
                                  products pairs paths trees nothing one sums
                                  numbers operations subuniverses constant)
  (let p-⨾ = Typing.p-⨾ R lifting products pairs paths trees nothing one
               sums numbers operations subuniverses constant)
  (let weaken-cons = Typing.weaken-cons R lifting products pairs paths trees
                       nothing one sums numbers operations subuniverses
                         constant)
  (let weaken-cons-stable = Typing.weaken-cons-stable R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  (let rename-stable = Typing.rename-stable R lifting products pairs paths
                         trees nothing one sums numbers operations subuniverses
                           constant)
  (let application-stable = Products.application-stable R lifting products
                              pairs paths trees nothing one sums numbers
                              operations subuniverses constant)
  (let supremum-stable = Trees.supremum-stable R lifting products pairs paths
                           trees nothing one sums numbers operations
                             subuniverses constant)
  where

  ----------------------------------------------------------------------
  -- The children's type

  children-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (Z : Ob) (x : Tm Z) (E : Vec (Tm Z) n)
    → meaning
        (Formers.pi k (m ⊔ℕ k) B
          (Formers.weaken (Formers.weaken (Formers.tree m k A B))))
        Z (x ∷ E)
      ＝ pi k (m ⊔ℕ k) (meaning B Z (x ∷ E))
          (meaning (Formers.tree m k A B) (Z ▸ meaning B Z (x ∷ E))
            (E [ p ]ᵉ))
  children-value m k A B Z x E =
    let b = meaning B Z (x ∷ E)
        T = Formers.tree m k A B
    in ap (pi k (m ⊔ℕ k) b)
         (bound-meaning 1 (Formers.weaken (Formers.weaken T)) (Z ▸ b)
             (ext b (x ∷ E)) ∙
           (weaken-cons (Formers.weaken T) (Z ▸ b) (q b)
               (x [ p ] ∷ E [ p ]ᵉ) ∙
             weaken-cons T (Z ▸ b) (x [ p ]) (E [ p ]ᵉ)))

  ----------------------------------------------------------------------
  -- The hypotheses' type

  -- B x, read over the extension by B x itself and past f.
  position-past :
    {n : ℕ} (B : Raw.Expression C (suc n)) (Z : Ob) (f x : Tm Z)
    (E : Vec (Tm Z) n) → Stable (meaning B) Z (x ∷ E)
    → meaning (Formers.weaken (Formers.weaken B)) (Z ▸ meaning B Z (x ∷ E))
        (ext (meaning B Z (x ∷ E)) (f ∷ x ∷ E))
      ＝ meaning B Z (x ∷ E) [ p ]
  position-past B Z f x E sB =
    let b = meaning B Z (x ∷ E)
    in weaken-cons (Formers.weaken B) (Z ▸ b) (q b)
           (f [ p ] ∷ x [ p ] ∷ E [ p ]ᵉ) ∙
         (weaken-cons B (Z ▸ b) (f [ p ]) (x [ p ] ∷ E [ p ]ᵉ) ∙
           sB (Z ▸ b) p)

  -- W A B, read past f, the new variable of B x and one more binder b′.
  tree-past :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B : Raw.Expression C (suc n)) (Z : Ob) (f x : Tm Z) (E : Vec (Tm Z) n)
    → Stable (meaning (Formers.tree m k A B)) Z E
    → (b′ : Tm (Z ▸ meaning B Z (x ∷ E)))
    → meaning
        (Formers.weaken
          (Formers.weaken
            (Formers.weaken (Formers.weaken (Formers.tree m k A B)))))
        (Z ▸ meaning B Z (x ∷ E) ▸ b′)
        (ext b′ (ext (meaning B Z (x ∷ E)) (f ∷ x ∷ E)))
      ＝ meaning (Formers.tree m k A B) Z E [ p ] [ p ]
  tree-past m k A B Z f x E sT b′ =
    let b = meaning B Z (x ∷ E)
        T = Formers.tree m k A B
        v = meaning T Z E
    in weaken-cons
           (Formers.weaken (Formers.weaken (Formers.weaken T)))
           (Z ▸ b ▸ b′) (q b′)
           (q b [ p ] ∷ f [ p ] [ p ] ∷ x [ p ] [ p ] ∷ E [ p ]ᵉ [ p ]ᵉ) ∙
         (weaken-cons (Formers.weaken (Formers.weaken T)) (Z ▸ b ▸ b′)
             (q b [ p ]) (f [ p ] [ p ] ∷ x [ p ] [ p ] ∷ E [ p ]ᵉ [ p ]ᵉ) ∙
           (weaken-cons (Formers.weaken T) (Z ▸ b ▸ b′) (f [ p ] [ p ])
               (x [ p ] [ p ] ∷ E [ p ]ᵉ [ p ]ᵉ) ∙
             (weaken-cons T (Z ▸ b ▸ b′) (x [ p ] [ p ]) (E [ p ]ᵉ [ p ]ᵉ) ∙
               (ap (meaning T (Z ▸ b ▸ b′))
                   (Environment.[]ᵉ-∘ R E p p ⁻¹) ∙
                 (sT (Z ▸ b ▸ b′) (p ∘ p) ∙ [∘] v p p)))))

  hypotheses-value :
    {n : ℕ} (m k l : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n)) (Z : Ob) (f x : Tm Z)
    (E : Vec (Tm Z) n)
    → Stable (meaning B) Z (x ∷ E) → Code R k (meaning B Z (x ∷ E))
    → Stable (meaning (Formers.tree m k A B)) Z E
    → Code R (m ⊔ℕ k) (meaning (Formers.tree m k A B) Z E)
    → type-of f
      ＝ pi k (m ⊔ℕ k) (meaning B Z (x ∷ E))
          (meaning (Formers.tree m k A B) Z E [ p ])
    → let b = meaning B Z (x ∷ E)
          v = meaning (Formers.tree m k A B) Z E
      in meaning
           (Formers.pi k l (Formers.weaken B)
             (Formers.instantiate-past 3 M
               (Formers.application k (m ⊔ℕ k)
                 (Formers.weaken (Formers.weaken B))
                 (Formers.weaken
                   (Formers.weaken
                     (Formers.weaken
                       (Formers.weaken (Formers.tree m k A B)))))
                 (Tree.hole (fsuc fzero)) (Tree.hole fzero))))
           Z (f ∷ x ∷ E)
         ＝ pi k l b
             (meaning M (Z ▸ b)
               (application k (m ⊔ℕ k) (b [ p ]) (v [ p ] [ p ]) (f [ p ])
                  (q b)
                ∷ E [ p ]ᵉ))
  hypotheses-value {n} m k l A B M Z f x E sB cB sT cT tf =
    let b = meaning B Z (x ∷ E)
        T = Formers.tree m k A B
        v = meaning T Z E
        B₂ = Formers.weaken (Formers.weaken B)
        T₄ = Formers.weaken
               (Formers.weaken (Formers.weaken (Formers.weaken T)))
        app = Formers.application k (m ⊔ℕ k) B₂ T₄
                (Tree.hole (fsuc fzero)) (Tree.hole fzero)
        IP = Formers.instantiate-past 3 M app
        env₁ = ext b (f ∷ x ∷ E)
        b₂ = meaning B₂ (Z ▸ b) env₁
        eb₂ = position-past B Z f x E sB
        cbp = code-[] R k b p cB
        e₁ = q-type k (b [ p ]) cbp ∙ [∘] b p p ⁻¹
        domain-values =
          ap
              (λ b′ → pi k (m ⊔ℕ k) b′ (meaning T₄ (Z ▸ b ▸ b′) (ext b′ env₁)))
              eb₂ ∙
            ap (pi k (m ⊔ℕ k) (b [ p ]))
              (tree-past m k A B Z f x E sT (b [ p ]))
        tf₁ = type-of-[] f p ∙
                (ap (λ s → s [ p ]) tf ∙
                  (pi-[] k (m ⊔ℕ k) b (v [ p ]) p cB
                      (code-[] R (m ⊔ℕ k) v p cT) ∙
                    ap (pi k (m ⊔ℕ k) (b [ p ]))
                      (p-⨾ b v (p ∘ p) (q (b [ p ])) e₁ ∙
                        [∘] v p p)))
        s-app = application-stable k (m ⊔ℕ k) B₂ T₄
                  (Tree.hole (fsuc fzero)) (Tree.hole fzero)
                  (Z ▸ b) env₁
                  (weaken-stable (Formers.weaken B) Z b (f ∷ x ∷ E)
                    (weaken-cons-stable B Z f (x ∷ E) sB))
                  (transport (Code R k) (eb₂ ⁻¹) cbp)
                  (weaken-stable
                    (Formers.weaken (Formers.weaken (Formers.weaken T)))
                    (Z ▸ b) b₂ env₁
                    (weaken-stable (Formers.weaken (Formers.weaken T)) Z b
                      (f ∷ x ∷ E)
                      (weaken-cons-stable (Formers.weaken T) Z f (x ∷ E)
                        (weaken-cons-stable T Z x E sT))))
                  (transport (Code R (m ⊔ℕ k))
                    (tree-past m k A B Z f x E sT b₂ ⁻¹)
                    (code-[] R (m ⊔ℕ k) (v [ p ]) p
                      (code-[] R (m ⊔ℕ k) v p cT)))
                  (Environment.stable-lookup R (fsuc fzero) (Z ▸ b) env₁)
                  (tf₁ ∙ domain-values ⁻¹)
                  (Environment.stable-lookup R fzero (Z ▸ b) env₁)
                  (q-type k b cB ∙ eb₂ ⁻¹)
        app-value =
          ap
              (λ b′ → application k (m ⊔ℕ k) b′
                 (meaning
                   (Binding.bound (Raw.binding C) (suc (suc (suc n))) 1 T₄)
                   (Z ▸ b ▸ b′) (ext b′ env₁))
                 (f [ p ]) (q b))
              eb₂ ∙
            ap (λ c → application k (m ⊔ℕ k) (b [ p ]) c (f [ p ]) (q b))
              (bound-meaning 1 T₄ (Z ▸ b ▸ b [ p ]) (ext (b [ p ]) env₁) ∙
                tree-past m k A B Z f x E sT (b [ p ]))
    in ap
           (λ b′ → pi k l b′
              (meaning (Binding.bound (Raw.binding C) (suc (suc n)) 1 IP)
                (Z ▸ b′) (ext b′ (f ∷ x ∷ E))))
           (weaken-cons B Z f (x ∷ E)) ∙
         ap (pi k l b)
           (bound-meaning 1 IP (Z ▸ b) env₁ ∙
             (instantiate-past-value 3 M app (Z ▸ b) env₁ s-app ∙
               ap₂ (λ y es → meaning M (Z ▸ b) (y ∷ es)) app-value
                 (tabulate-lookup (E [ p ]ᵉ))))

  ----------------------------------------------------------------------
  -- The method's type

  -- B, weakened past three variables under its own binder, read at an
  -- extension: B at the extension of the remaining environment.
  position-skip :
    {n : ℕ} (B : Raw.Expression C (suc n)) (Z : Ob) (h f x : Tm Z)
    (E : Vec (Tm Z) n) (a : Tm Z)
    → meaning (Formers.weaken-past n 1 3 B) (Z ▸ a) (ext a (h ∷ f ∷ x ∷ E))
      ＝ meaning B (Z ▸ a) (ext a E)
  position-skip {n} B Z h f x E a =
    rename-value (Binding.lift (Raw.binding C) 1 (λ (y : Fin n) → 3 ↑ʳ y))
        B (Z ▸ a) (ext a (h ∷ f ∷ x ∷ E)) ∙
      ap (λ es → meaning B (Z ▸ a) (q a ∷ es)) (tabulate-lookup (E [ p ]ᵉ))

  method-type-value :
    {n : ℕ} (m k : ℕ) (A : Raw.Expression C n)
    (B M : Raw.Expression C (suc n)) (Z : Ob) (h f x : Tm Z)
    (E : Vec (Tm Z) n)
    → Stable (meaning A) Z E → Code R m (meaning A Z E)
    → Stable (meaning B) (Z ▸ meaning A Z E) (ext (meaning A Z E) E)
    → Code R k (meaning B (Z ▸ meaning A Z E) (ext (meaning A Z E) E))
    → type-of x ＝ meaning A Z E
    → type-of f
      ＝ pi k (m ⊔ℕ k)
          (meaning B (Z ▸ meaning A Z E) (ext (meaning A Z E) E) [ id ⨾ x ])
          (tree m k (meaning A Z E)
             (meaning B (Z ▸ meaning A Z E) (ext (meaning A Z E) E)) [ p ])
    → meaning (Block.method-type m k A B M) Z (h ∷ f ∷ x ∷ E)
      ＝ meaning M Z
          (supremum m k (meaning A Z E)
             (meaning B (Z ▸ meaning A Z E) (ext (meaning A Z E) E)) x f
           ∷ E)
  method-type-value {n} m k A B M Z h f x E sA cA sB cB tx tf =
    let α = meaning A Z E
        env₃ = h ∷ f ∷ x ∷ E
        A₃ = Formers.weaken (Formers.weaken (Formers.weaken A))
        B₃ = Formers.weaken-past n 1 3 B
        S = Formers.supremum m k A₃ B₃
              (Tree.hole (fsuc (fsuc fzero)))
              (Tree.hole (fsuc fzero))
        a₃ = meaning A₃ Z env₃
        ea₃ = weaken-cons (Formers.weaken (Formers.weaken A)) Z h
                      (f ∷ x ∷ E) ∙
                (weaken-cons (Formers.weaken A) Z f (x ∷ E) ∙
                  weaken-cons A Z x E)
        sB₃ = rename-stable
                (Binding.lift (Raw.binding C) 1 (λ (y : Fin n) → 3 ↑ʳ y)) B
                (Z ▸ a₃) (ext a₃ env₃)
                (transport (Stable (meaning B) (Z ▸ a₃))
                  (ap (λ es → q a₃ ∷ es) (tabulate-lookup (E [ p ]ᵉ) ⁻¹))
                  (transport (λ a′ → Stable (meaning B) (Z ▸ a′) (ext a′ E))
                    (ea₃ ⁻¹) sB))
        cB₃ = transport (Code R k) (position-skip B Z h f x E a₃ ⁻¹)
                (transport (λ a′ → Code R k (meaning B (Z ▸ a′) (ext a′ E)))
                  (ea₃ ⁻¹) cB)
        tf₃ = transport
                (λ a′ → type-of f
                   ＝ pi k (m ⊔ℕ k)
                       (meaning B₃ (Z ▸ a′) (ext a′ env₃) [ id ⨾ x ])
                       (tree m k a′ (meaning B₃ (Z ▸ a′) (ext a′ env₃)) [ p ]))
                (ea₃ ⁻¹)
                (tf ∙
                  ap
                    (λ b′ → pi k (m ⊔ℕ k) (b′ [ id ⨾ x ]) (tree m k α b′ [ p ]))
                    (position-skip B Z h f x E α ⁻¹))
        sS = supremum-stable m k A₃ B₃
               (Tree.hole (fsuc (fsuc fzero)))
               (Tree.hole (fsuc fzero)) Z env₃
               (weaken-cons-stable (Formers.weaken (Formers.weaken A)) Z h
                 (f ∷ x ∷ E)
                 (weaken-cons-stable (Formers.weaken A) Z f (x ∷ E)
                   (weaken-cons-stable A Z x E sA)))
               (transport (Code R m) (ea₃ ⁻¹) cA) sB₃ cB₃
               (Environment.stable-lookup R (fsuc (fsuc fzero)) Z env₃)
               (tx ∙ ea₃ ⁻¹)
               (Environment.stable-lookup R (fsuc fzero) Z env₃) tf₃
        S-value =
          ap
              (λ a′ → supremum m k a′
                 (meaning
                   (Binding.bound (Raw.binding C) (suc (suc (suc n))) 1 B₃)
                   (Z ▸ a′) (ext a′ env₃))
                 x f)
              ea₃ ∙
            ap (λ b′ → supremum m k α b′ x f)
              (bound-meaning 1 B₃ (Z ▸ α) (ext α env₃) ∙
                position-skip B Z h f x E α)
    in instantiate-past-value 3 M S Z env₃ sS ∙
         ap₂ (λ y es → meaning M Z (y ∷ es)) S-value (tabulate-lookup E)
