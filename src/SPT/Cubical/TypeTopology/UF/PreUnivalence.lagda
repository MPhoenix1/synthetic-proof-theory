Martin Escardo 23 February 2023

The pre-univalence axiom, first suggested by Evan Cavallo in November
2017 [1] and then again by Peter Lumsdaine in August 2022
verbally to me.

[1] https://groups.google.com/g/homotopytypetheory/c/bKti7krHM-c/m/vxRU3FwADQAJ

The preunivalence axiom is a common generalization of the univalence
axiom and the K axiom.

The strong preunivalence axiom is a variant that was stated by Fredrik Bakke
in the agda-unimath in February 2025 [2].

[2] https://unimath.github.io/agda-unimath/foundation.strong-preunivalence.html

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.UF.PreUnivalence where

open import SPT.Cubical.TypeTopology.MLTT.Spartan
open import SPT.Cubical.TypeTopology.UF.Base
open import SPT.Cubical.TypeTopology.UF.Embeddings
open import SPT.Cubical.TypeTopology.UF.Equiv
open import SPT.Cubical.TypeTopology.UF.Equiv-FunExt
open import SPT.Cubical.TypeTopology.UF.EquivalenceExamples
open import SPT.Cubical.TypeTopology.UF.FunExt
open import SPT.Cubical.TypeTopology.UF.Retracts
open import SPT.Cubical.TypeTopology.UF.Sets
open import SPT.Cubical.TypeTopology.UF.Subsingletons
open import SPT.Cubical.TypeTopology.UF.Univalence

is-preunivalent : ∀ 𝓤 → 𝓤 ⁺ ̇
is-preunivalent 𝓤 = (X Y : 𝓤 ̇ ) → is-embedding (idtoeq X Y)

Preunivalence : 𝓤ω
Preunivalence = (𝓤 : Universe) → is-preunivalent 𝓤

univalence-gives-preunivalence : is-univalent 𝓤
                               → is-preunivalent 𝓤
univalence-gives-preunivalence ua X Y = equivs-are-embeddings
                                         (idtoeq X Y)
                                         (ua X Y)

Univalence-gives-Preunivalence : Univalence → Preunivalence
Univalence-gives-Preunivalence ua 𝓤 = univalence-gives-preunivalence (ua 𝓤)

K-gives-preunivalence : K-axiom 𝓤
                      → K-axiom (𝓤 ⁺)
                      → is-preunivalent 𝓤
K-gives-preunivalence {𝓤} k k' X Y e (p , _) (p' , _) =
 to-subtype-＝ (λ _ → k (X ≃ Y)) (k' (𝓤 ̇ )p p')

K-gives-Preunivalence : K-Axiom → Preunivalence
K-gives-Preunivalence k 𝓤 = K-gives-preunivalence (k 𝓤) (k (𝓤 ⁺))

\end{code}

Added by Evan Cavallo on 13th March 2025. The strong preunivalence axiom and the
fact that it implies the preunivalence axiom are due to Fredrik Bakke.

\begin{code}

is-strong-preunivalent : ∀ 𝓤 𝓥 → Set (𝓤 ⁺ ⊔ 𝓥 ⁺)
is-strong-preunivalent 𝓤 𝓥 = (X : 𝓤 ̇ ) → is-set (Σ Y ꞉ 𝓥 ̇  , X ≃ Y)

strong-preunivalence-gives-preunivalence : is-strong-preunivalent 𝓤 𝓤
                                         → is-preunivalent 𝓤
strong-preunivalence-gives-preunivalence spua X =
 NatΣ-is-embedding-converse (X ＝_) (X ≃_) (idtoeq X)
  (maps-of-props-into-sets-are-embeddings
   (NatΣ (idtoeq X))
    (singleton-types-are-props X)
     (spua X))

funext-and-preunivalence-give-strong-preunivalence : funext 𝓤 𝓤
                                                   → funext 𝓥 𝓤
                                                   → funext 𝓥 𝓥
                                                   → is-preunivalent 𝓥
                                                   → is-strong-preunivalent 𝓤 𝓥
funext-and-preunivalence-give-strong-preunivalence
 {𝓤} {𝓥} feuu fevu fevv preua X {Y , α} {Y' , α'} =
 retract-of-prop
  (to-Σ-＝ , from-Σ-＝ , tofrom-Σ-＝)
   (equiv-to-prop
    (Σ-cong λ p →
     (_ , ∙-is-equiv-left (transport-eq p)) ● shift-equiv α (idtoeq _ _ p) α')
    (preua _ _ (≃-sym α ● α')))
 where
  transport-eq : (p : Y ＝ Y') → α ● idtoeq Y Y' p ＝ transport (X ≃_) p α
  transport-eq refl = ≃-refl-right' fevu fevv feuu α

  shift-equiv : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓥 ̇ }
              → (e : A ≃ B) (e' : B ≃ C) (e'' : A ≃ C)
              → (e ● e' ＝ e'') ≃ (e' ＝ ≃-sym e ● e'')
  shift-equiv e e' e'' =
   (e ● e' ＝ e'')
    ≃⟨ _ , ap-is-equiv (≃-sym e ●_) (pr₂ q) ⟩
   (≃-sym e ● (e ● e') ＝ ≃-sym e ● e'')
    ≃⟨ ＝-cong-l _ _ (≃-assoc' fevv fevv fevv (≃-sym e) e e') ⟩
   ((≃-sym e ● e) ● e' ＝ ≃-sym e ● e'')
    ≃⟨ ＝-cong-l _ _ (ap (_● e') (≃-sym-left-inverse' fevv e)) ⟩
   (≃-refl _ ● e' ＝ ≃-sym e ● e'')
    ≃⟨ ＝-cong-l _ _ (≃-refl-left' fevv fevv fevv e') ⟩
   (e' ＝ ≃-sym e ● e'') ■
   where
    q = ≃-cong-left' fevu fevv feuu fevv fevv e

\end{code}
