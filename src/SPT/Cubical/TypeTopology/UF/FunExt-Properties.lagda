Martin Escardo, 19th May 2018.

Properties of function extensionality.

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.UF.FunExt-Properties where

open import SPT.Cubical.TypeTopology.MLTT.Spartan
open import SPT.Cubical.TypeTopology.UF.Base
open import SPT.Cubical.TypeTopology.UF.FunExt
open import SPT.Cubical.TypeTopology.UF.Equiv
open import SPT.Cubical.TypeTopology.UF.Equiv-FunExt
open import SPT.Cubical.TypeTopology.UF.Yoneda
open import SPT.Cubical.TypeTopology.UF.Subsingletons
open import SPT.Cubical.TypeTopology.UF.Retracts

\end{code}

Vladimir Voevodsky proved in Coq that naive function extensionality
(any two pointwise equal non-dependent functions are equal) implies
function extensionality (happly is an equivalence, for dependent
functions):

  https://github.com/vladimirias/Foundations/blob/master/Generalities/uu0.v

Here is an Agda version, with explicit indication of the universe levels.

\begin{code}

naive-funext-gives-funext' : naive-funext 𝓤 (𝓤 ⊔ 𝓥) → naive-funext 𝓤 𝓤 → funext 𝓤 𝓥
naive-funext-gives-funext' {𝓤} {𝓥} nfe nfe' = funext-via-singletons γ
 where
  γ : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
    → ((x : X) → is-singleton (A x))
    → is-singleton (Π A)
  γ X A φ = δ
   where
    f : Σ A → X
    f = pr₁

    f-is-equiv : is-equiv f
    f-is-equiv = pr₁-is-equiv X A φ

    g : (X → Σ A) → (X → X)
    g h = f ∘ h

    g-is-equiv : is-equiv g
    g-is-equiv = equiv-post nfe nfe' f f-is-equiv

    e : ∃! h ꞉ (X → Σ A) , f ∘ h ＝ id
    e = equivs-are-vv-equivs g g-is-equiv id

    r : (Σ h ꞉ (X → Σ A) , f ∘ h ＝ id) → Π A
    r (h , p) x = transport A (happly p x) (pr₂ (h x))

    s : Π A → (Σ h ꞉ (X → Σ A) , f ∘ h ＝ id)
    s φ = (λ x → x , φ x) , refl

    rs : ∀ φ → r (s φ) ＝ φ
    rs φ = refl

    δ : is-singleton (Π A)
    δ = retract-of-singleton (r , s , rs) e

naive-funext-gives-funext : naive-funext 𝓤 𝓤 → funext 𝓤 𝓤
naive-funext-gives-funext fe = naive-funext-gives-funext' fe fe

naive-funext-gives-funext₀ : naive-funext 𝓤 𝓤 → funext 𝓤 𝓤₀
naive-funext-gives-funext₀ fe = naive-funext-gives-funext' fe fe

\end{code}

Added by Evan Cavallo on 13th March 2025.

The equivalence extensionality axiom is the restriction of function
extensionality to equivalences. By an argument similar to the proof of function
extensionality from univalence, it implies full function extensionality.

\begin{code}

equivext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
equivext 𝓤 𝓥 =
 {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α β : X ≃ Y)
 → is-equiv (λ (p : α ＝ β) → happly (ap ⌜_⌝ p))

equivext-gives-funext : equivext 𝓤 𝓤 → funext 𝓤 𝓤
equivext-gives-funext {𝓤} ee =
 funext-via-singletons main
 where
  promote : (A : 𝓤 ̇ ) {X Y : 𝓤 ̇ } → X ≃ Y → (A ≃ X) ≃ (A ≃ Y)
  promote A α =
   qinveq
    (_● α)
    ( (_● ≃-sym α)
    , (λ β → inverse _ (ee _ _) (inverses-are-retractions _ (pr₂ α) ∘ ⌜ β ⌝))
    , (λ γ → inverse _ (ee _ _) (inverses-are-sections _ (pr₂ α) ∘ ⌜ γ ⌝)))

  module _ (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) (cY : (x : X) → is-singleton (Y x)) where
   π : (Σ Y) ≃ X
   π =
    qinveq
     pr₁
     ( (λ x → x , pr₁ (cY x))
     , (λ (x , y) → to-Σ-＝ (refl , pr₂ (cY x) y))
     , ∼-refl)

   sec : Π Y → fiber ⌜ promote X π ⌝ 𝕚𝕕
   sec f =
    ( qinveq
       (λ x → x , f x)
       ( pr₁
       , ∼-refl
       , (λ (x , y) → to-Σ-＝ (refl , singletons-are-props (cY x) _ _)))
    , inverse _ (ee _ _) ∼-refl)

   ret : fiber ⌜ promote X π ⌝ 𝕚𝕕 → Π Y
   ret (α , p) x = transport Y (happly (ap ⌜_⌝ p) x) (pr₂ (pr₁ α x))

   inv : ret ∘ sec ∼ id
   inv f =
    ap (λ h → λ x → transport Y (h x) (pr₂ (pr₁ α x))) cancel
     where
      α = pr₁ (sec f)
      p = pr₂ (sec f)

      cancel : happly (ap ⌜_⌝ p) ＝ ∼-refl
      cancel = inverses-are-sections _ (ee _ _) (∼-refl)

   main : is-singleton (Π Y)
   main = retract-of-singleton
           (ret , sec , inv)
           (equivs-are-vv-equivs _ (pr₂ (promote X π)) 𝕚𝕕)

\end{code}

End of addition.
