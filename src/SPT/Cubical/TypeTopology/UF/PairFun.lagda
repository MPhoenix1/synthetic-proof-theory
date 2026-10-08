Martin Escardo 2011.

Extended 2018 with more properties of the function pair-fun.

Combining two functions to get a function Σ A → Σ B, and properties of
the resulting function.

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.TypeTopology.UF.PairFun where

open import SPT.Cubical.TypeTopology.MLTT.Spartan
open import SPT.Cubical.TypeTopology.TypeTopology.Density

open import SPT.Cubical.TypeTopology.UF.Embeddings
open import SPT.Cubical.TypeTopology.UF.Equiv
open import SPT.Cubical.TypeTopology.UF.EquivalenceExamples
open import SPT.Cubical.TypeTopology.UF.Subsingletons

module _ {𝓤 𝓥 𝓦 𝓣}
         {X : 𝓤 ̇ }
         {A : X → 𝓥 ̇ }
         {Y : 𝓦 ̇ }
         {B : Y → 𝓣 ̇ }
         (f : X → Y)
         (g : (x : X) → A x → B (f x))
       where

 pair-fun : Σ A → Σ B
 pair-fun (x , a) = (f x , g x a)

 pair-fun-fiber' : (y : Y) → B y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 pair-fun-fiber' y b = Σ (x , a) ꞉ fiber f y , fiber (g x) (transport⁻¹ B a b)

 pair-fun-fiber-≃ : (y : Y) (b : B y)
                  → fiber pair-fun (y , b)
                  ≃ pair-fun-fiber' y b
 pair-fun-fiber-≃  y b = qinveq φ (γ , γφ , φγ)
  where
   φ : fiber pair-fun (y , b) → pair-fun-fiber' y b
   φ ((x , a) , refl) = (x , refl) , (a , refl)

   γ : pair-fun-fiber' y b → fiber pair-fun (y , b)
   γ ((x , refl) , (a , refl)) = (x , a) , refl

   γφ : (t : fiber pair-fun (y , b)) → γ (φ t) ＝ t
   γφ ((x , a) , refl) = refl

   φγ : (s : pair-fun-fiber' y b) → φ (γ s) ＝ s
   φγ ((x , refl) , (a , refl)) = refl


 pair-fun-is-embedding : is-embedding f
                       → ((x : X) → is-embedding (g x))
                       → is-embedding pair-fun
 pair-fun-is-embedding e d (y , b) = h
  where
   i : is-prop (pair-fun-fiber' y b)
   i = subtypes-of-props-are-props'
        pr₁
        (pr₁-lc (λ {w} → d (pr₁ w) (transport⁻¹ B (pr₂ w) b)))
        (e y)

   h : is-prop (fiber pair-fun (y , b))
   h = equiv-to-prop (pair-fun-fiber-≃ y b) i

 pair-fun-is-vv-equiv : is-vv-equiv f
                      → ((x : X) → is-vv-equiv (g x))
                      → is-vv-equiv pair-fun
 pair-fun-is-vv-equiv e d (y , b) = h
  where
   k : is-prop (fiber pair-fun (y , b))
   k = pair-fun-is-embedding
        (equivs-are-embeddings f (vv-equivs-are-equivs f e))
        (λ x → equivs-are-embeddings (g x) (vv-equivs-are-equivs (g x) (d x)))
        (y , b)

   x : X
   x = fiber-point (center (e y))

   i : f x ＝ y
   i = fiber-identification (center (e y))

   w : pair-fun-fiber' y b
   w = (center (e y) , center (d x (transport⁻¹ B i b)))

   h : is-singleton (fiber pair-fun (y , b))
   h = pointed-props-are-singletons (⌜ pair-fun-fiber-≃ y b ⌝⁻¹ w) k

 pair-fun-is-equiv : is-equiv f
                   → ((x : X) → is-equiv (g x))
                   → is-equiv pair-fun
 pair-fun-is-equiv e d = vv-equivs-are-equivs
                          pair-fun
                          (pair-fun-is-vv-equiv
                            (equivs-are-vv-equivs f e)
                            (λ x → equivs-are-vv-equivs (g x) (d x)))

 pair-fun-dense : is-dense f
                → ((x : X) → is-dense (g x))
                → is-dense pair-fun
 pair-fun-dense i j = contrapositive γ i
  where
   γ : (Σ w ꞉ Σ B , ¬ fiber pair-fun w) → Σ y ꞉ Y , ¬ fiber f y
   γ ((y , b) , n) = y , m
    where
     m : ¬ fiber f y
     m (x , refl) = j x (b , l)
      where
       l : ¬ fiber (g x) b
       l (a , refl) = n ((x , a) , refl)

 open import SPT.Cubical.TypeTopology.UF.PropTrunc

 module pair-fun-surjection (pt : propositional-truncations-exist) where

  open PropositionalTruncation pt
  open import SPT.Cubical.TypeTopology.UF.ImageAndSurjection pt

  pair-fun-is-surjection : is-surjection f
                         → ((x : X) → is-surjection (g x))
                         → is-surjection pair-fun
  pair-fun-is-surjection s t (y , b) = γ
   where
    γ : ∃ (x , a) ꞉ Σ A , (pair-fun (x , a) ＝ y , b)
    γ = ∥∥-rec ∃-is-prop
         (λ {(x , refl) → ∥∥-rec ∃-is-prop
                           (λ {(a , refl) → ∣ (x , a) , refl ∣})
                           (t x b)})
         (s y)

pair-fun-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                 {Y : 𝓦 ̇ } {B : Y → 𝓣 ̇ }
                 (f : X ≃ Y)
               → ((x : X) → A x ≃ B (⌜ f ⌝ x))
               → Σ A ≃ Σ B
pair-fun-equiv f g = pair-fun ⌜ f ⌝ (λ x → ⌜ g x ⌝) ,
                     pair-fun-is-equiv _ _ ⌜ f ⌝-is-equiv (λ x → ⌜ g x ⌝-is-equiv)

Σ-change-of-variable-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                 (A : X → 𝓦 ̇ ) (g : Y → X)
                               → is-embedding g
                               → (Σ y ꞉ Y , A (g y)) ↪ (Σ x ꞉ X , A x)
Σ-change-of-variable-embedding A g e = pair-fun g (λ _ → id) ,
                                       pair-fun-is-embedding
                                        g
                                        (λ _ → id)
                                        e
                                        (λ _ → id-is-embedding)

pair-fun-embedding : {X : 𝓤 ̇ }
                     {A : X → 𝓥 ̇ }
                     {Y : 𝓦 ̇ }
                     {B : Y → 𝓣 ̇ }
                   → (e : X ↪ Y)
                   → ((x : X) → A x ↪ B (⌊ e ⌋ x))
                   → Σ A ↪ Σ B
pair-fun-embedding (f , i) g = pair-fun f (λ x → ⌊ g x ⌋) ,
                               pair-fun-is-embedding
                                f
                                ((λ x → ⌊ g x ⌋))
                                i
                                (λ x → ⌊ g x ⌋-is-embedding)


pair-fun-is-embedding-special : {𝓤 𝓥 𝓦 : Universe}
                                {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {B : Y → 𝓦 ̇ }
                              → (f : X → Y)
                              → (g : (x : X) → B (f x))
                              → is-embedding f
                              → ((y : Y) → is-prop (B y))
                              → is-embedding (λ x → f x , g x)
pair-fun-is-embedding-special {𝓤} {𝓥} {𝓦} {X} {Y} {B} f g f-emb B-is-prop = e
 where
  k : X ≃ X × 𝟙 {𝓤}
  k = ≃-sym 𝟙-rneutral

  k-emb : is-embedding ⌜ k ⌝
  k-emb = equivs-are-embeddings ⌜ k ⌝ ⌜ k ⌝-is-equiv

  h : X → Σ B
  h x = f x , g x

  g' : (x : X) → 𝟙 → B (f x)
  g' x _ = g x

  g'-emb : (x : X) → is-embedding (g' x)
  g'-emb x = maps-of-props-are-embeddings (g' x) 𝟙-is-prop (B-is-prop (f x))

  remark : h ＝ pair-fun f g' ∘ ⌜ k ⌝
  remark = refl

  e : is-embedding h
  e = ∘-is-embedding k-emb (pair-fun-is-embedding f g' f-emb g'-emb)

\end{code}
