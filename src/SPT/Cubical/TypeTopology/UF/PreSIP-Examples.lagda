Martin Escardo, 24 Feb 2023

Modified from SIP-Examples. Only the examples we need are included for the moment.

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.UF.PreSIP-Examples where

open import SPT.Cubical.TypeTopology.MLTT.Spartan

open import SPT.Cubical.TypeTopology.UF.Base
open import SPT.Cubical.TypeTopology.UF.PreSIP
open import SPT.Cubical.TypeTopology.UF.Equiv
open import SPT.Cubical.TypeTopology.UF.Equiv-FunExt
open import SPT.Cubical.TypeTopology.UF.PreUnivalence
open import SPT.Cubical.TypeTopology.UF.EquivalenceExamples
open import SPT.Cubical.TypeTopology.UF.Subsingletons
open import SPT.Cubical.TypeTopology.UF.Subsingletons-FunExt
open import SPT.Cubical.TypeTopology.UF.Embeddings
open import SPT.Cubical.TypeTopology.UF.FunExt

module generalized-metric-space
        {𝓤 𝓥 𝓦  : Universe}
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → (X → X → R) → 𝓦 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (d : X → X → R) → is-prop (axioms X d))
       where

 open presip
 open presip-with-axioms

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → X → R

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , d) (Y , e) (f , _) = (d ＝ λ x x' → e (f x) (f x'))

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , d) = 𝓻𝓮𝒻𝓵 d

   h : {X : 𝓤 ̇ } {d e : S X} → canonical-map ι ρ d e ∼ -id (d ＝ e)
   h (refl {d}) = 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 d)

   θ : {X : 𝓤 ̇ } (d e : S X) → is-embedding (canonical-map ι ρ d e)
   θ d e = equivs-are-embeddings
            (canonical-map ι ρ d e)
            (equiv-closed-under-∼ id
              (canonical-map ι ρ d e)
              (id-is-equiv (d ＝ e))
              h)

 M : 𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓦 ̇
 M = Σ X ꞉ 𝓤 ̇ , Σ d ꞉ (X → X → R) , axioms X d

 _≅₀_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅₀ (Y , e , _) = Σ f ꞉ (X → Y)
                                  , is-equiv f
                                  × (d ＝ λ x x' → e (f x) (f x'))

 M-embedding₀ : is-preunivalent 𝓤 → (A B : M) → (A ＝ B) ↪ (A ≅₀ B)
 M-embedding₀ pua = ＝-embedding-with-axioms pua sns-data axioms axiomss

 _≅₁_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅₁ (Y , e , _) = Σ f ꞉ (X → Y)
                                  , is-equiv f
                                  × ((x x' : X) → d x x' ＝ e (f x) (f x'))

 ≅₀-coincides-with-≅₁ : Fun-Ext → (A B : M) → (A ≅₀ B) ≃ (A ≅₁ B)
 ≅₀-coincides-with-≅₁ fe (X , d , _) (Y , e , _) =
  Σ-cong (λ f → ×-cong
                 (≃-refl (is-equiv f))
                 (≃-funext₂ fe fe d (λ x x' → e (f x) (f x'))))

 M-embedding₁ : is-preunivalent 𝓤
              → Fun-Ext
              → (A B : M) → (A ＝ B) ↪ (A ≅₁ B)
 M-embedding₁ pua fe A B = (A ＝ B) ↪⟨ M-embedding₀ pua A B ⟩
                           (A ≅₀ B) ↪⟨ ≃-gives-↪ (≅₀-coincides-with-≅₁ fe A B) ⟩
                           (A ≅₁ B) □

module relational-space
        {𝓤 𝓥 𝓦 : Universe}
        (axioms  : (X : 𝓤 ̇ ) → (X → X → 𝓥 ̇ ) → 𝓦 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (R : X → X → 𝓥 ̇ ) → is-prop (axioms X R))
        (rel-is-prop-valued : ∀ {X R} → axioms X R → ∀ {x y} → is-prop (R x y))
       where

 open presip
 open presip-with-axioms
 open generalized-metric-space (𝓥 ̇ ) axioms axiomss

 _≅₂_ : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , R , _) ≅₂ (Y , S , _) = Σ f ꞉ (X → Y)
                                  , is-equiv f
                                  × ((x x' : X) → R x x' ↔ S (f x) (f x'))

 ≅₁-coincides-with-≅₂ : Fun-Ext
                      → Prop-Ext
                      → (A B : M) → (A ≅₁ B) ≃ (A ≅₂ B)
 ≅₁-coincides-with-≅₂ fe pe A@(X , R , a) B@(Y , S , b) =
  Σ-cong
   (λ f → ×-cong
           (≃-refl (is-equiv f))
           (Π-cong' fe (λ x →
            Π-cong' fe (λ x' →
             prop-＝-≃-↔ pe fe
              (rel-is-prop-valued a)
              (rel-is-prop-valued b)))))

 M-embedding₂ : is-preunivalent 𝓤
              → Fun-Ext
              → Prop-Ext
              → (A B : M) → (A ＝ B) ↪ (A ≅₂ B)
 M-embedding₂ pua fe pe A B =
  (A ＝ B) ↪⟨ M-embedding₁ pua fe A B ⟩
  (A ≅₁ B) ↪⟨ ≃-gives-↪ (≅₁-coincides-with-≅₂ fe pe A B) ⟩
  (A ≅₂ B) □

\end{code}

After a comment by Peter Lumsdaine, we don't need propositional
extensionality if we prove the above directly without the detour via
the equivalence:

\begin{code}

 ≅₁-embeds-into-≅₂ : is-preunivalent 𝓥
                   → Fun-Ext
                   → (A B : M) → (A ≅₁ B) ↪ (A ≅₂ B)
 ≅₁-embeds-into-≅₂ pua fe A@(X , R , a) B@(Y , S , b) =
  NatΣ-embedding
   (λ f → (λ (f-is-equiv , φ) → f-is-equiv , (λ x x' → g f x x' (φ x x'))) ,
          (×-is-embedding
            id
            (λ (φ : (x x' : X) → R x x' ＝ S (f x) (f x')) x x' → g f x x' (φ x x'))
            id-is-embedding
            (NatΠ-is-embedding
              (λ x → ∀ x' → R x x' ＝ S (f x) (f x'))
              (λ x → ∀ x' → R x x' ↔ S (f x) (f x'))
              (λ x (ψ : (x' : X) → R x x' ＝ S (f x) (f x')) → NatΠ (g f x) ψ)
              fe
              (λ x → NatΠ-is-embedding
                      (λ x' → R x x' ＝ S (f x) (f x'))
                      (λ x' → R x x' ↔ S (f x) (f x'))
                      (g f x)
                      fe
                      (g-is-embedding f x)))))
  where
   g : (f : X → Y) (x x' : X)
     → R x x' ＝ S (f x) (f x')
     → R x x' ↔ S (f x) (f x')
   g f x x' p = Idtofun p , Idtofun (p ⁻¹)

   g-is-embedding : (f : X → Y) (x x' : X)
                  → is-embedding (g f x x')
   g-is-embedding f x x' =
    maps-of-props-are-embeddings
     (g f x x')
     (subtypes-of-props-are-props
       (idtoeq (R x x') (S (f x) (f x')))
       (pua (R x x') (S (f x) (f x')))
       (Σ-is-prop
         (Π-is-prop fe (λ _ → rel-is-prop-valued b))
         (being-equiv-is-prop'' fe)))
       (×-is-prop
         (Π-is-prop fe (λ _ → rel-is-prop-valued b))
         (Π-is-prop fe (λ _ → rel-is-prop-valued a)))

 M-embedding₂-bis : is-preunivalent 𝓤
                  → is-preunivalent 𝓥
                  → Fun-Ext
                  → (A B : M) → (A ＝ B) ↪ (A ≅₂ B)
 M-embedding₂-bis pua pua' fe A B =
  (A ＝ B) ↪⟨ M-embedding₁ pua fe A B ⟩
  (A ≅₁ B) ↪⟨ ≅₁-embeds-into-≅₂ pua' fe A B ⟩
  (A ≅₂ B) □


\end{code}
