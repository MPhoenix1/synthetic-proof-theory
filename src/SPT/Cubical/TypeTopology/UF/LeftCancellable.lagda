Martin Escardo.

Properties of left cancellable maps.

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.UF.LeftCancellable where

open import SPT.Cubical.TypeTopology.MLTT.Spartan
open import SPT.Cubical.TypeTopology.UF.Base
open import SPT.Cubical.TypeTopology.UF.Subsingletons
open import SPT.Cubical.TypeTopology.UF.Retracts
open import SPT.Cubical.TypeTopology.UF.Equiv

left-cancellable-reflects-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                 → left-cancellable f
                                 → is-prop Y
                                 → is-prop X
left-cancellable-reflects-is-prop f lc i x x' = lc (i (f x) (f x'))

section-lc : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A)
           → is-section s
           → left-cancellable s
section-lc {𝓤} {𝓥} {X} {Y} s (r , rs) {x} {y} p = (rs x)⁻¹ ∙ ap r p ∙ rs y

is-equiv-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
            → is-equiv f
            → left-cancellable f
is-equiv-lc f (_ , hasr) = section-lc f hasr

left-cancellable-closed-under-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                                  (f : X → Y) (g : Y → Z)
                                → left-cancellable f
                                → left-cancellable g
                                → left-cancellable (g ∘ f)
left-cancellable-closed-under-∘ f g lcf lcg = lcf ∘ lcg

NatΣ-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } (f : Nat A B)
        → ((x : X) → left-cancellable(f x))
        → left-cancellable (NatΣ f)
NatΣ-lc {𝓤} {𝓥} {𝓦} {X} {A} {B} f flc {x , a} {x' , a'} p =
 to-Σ-＝ (ap pr₁ p , γ)
 where
  γ : transport A (ap pr₁ p) a ＝ a'
  γ = flc x' (f x' (transport A (ap pr₁ p) a) ＝⟨ nat-transport f (ap pr₁ p) ⟩
              transport B (ap pr₁ p) (f x a)  ＝⟨ from-Σ-＝' p ⟩
              f x' a'                         ∎)

NatΠ-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } (f : Nat A B)
        → ((x : X) → left-cancellable(f x))
        → {g g' : Π A} → NatΠ f g ＝ NatΠ f g' → g ∼ g'
NatΠ-lc f flc {g} {g'} p x = flc x (happly p x)

\end{code}

Sometimes the type of left cancellable maps is useful (but more often
the type of embeddings, defined elsewhere, is useful).

\begin{code}

_↣_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↣ Y =  Σ f ꞉ (X → Y) , left-cancellable f

⌈_⌉ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ↣ Y → X → Y
⌈ f , _ ⌉ = f

infix 0 _↣_

\end{code}
