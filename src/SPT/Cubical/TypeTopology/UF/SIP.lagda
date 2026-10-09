Martin Escardo, 30 April 2020

The structure identity principle and tools from the 2019 paper and links

 https://arxiv.org/abs/1911.00580
 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

There are three submodules:

 * sip
 * sip-with-axioms
 * sip-join

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.TypeTopology.UF.SIP where

open import SPT.Cubical.TypeTopology.MLTT.Spartan
open import SPT.Cubical.TypeTopology.UF.Base
open import SPT.Cubical.TypeTopology.UF.Embeddings
open import SPT.Cubical.TypeTopology.UF.Equiv
open import SPT.Cubical.TypeTopology.UF.EquivalenceExamples
open import SPT.Cubical.TypeTopology.UF.Retracts
open import SPT.Cubical.TypeTopology.UF.Subsingletons
open import SPT.Cubical.TypeTopology.UF.Univalence
open import SPT.Cubical.TypeTopology.UF.Yoneda

module sip where

 ⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
 ⟨ X , s ⟩ = X

 structure : {S : 𝓤 ̇ → 𝓥 ̇ } (A : Σ S) → S ⟨ A ⟩
 structure (X , s) = s

 canonical-map : {S : 𝓤 ̇ → 𝓥 ̇ }
                 (ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )
                 (ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩))
                 {X : 𝓤 ̇ }
                 (s t : S X)
               → s ＝ t → ι (X , s) (X , t) (≃-refl X)
 canonical-map ι ρ {X} s s (refl {s}) = ρ (X , s)

 SNS : (𝓤 ̇ → 𝓥 ̇ ) → (𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
 SNS {𝓤} {𝓥} S 𝓦 = Σ ι ꞉ ((A B : Σ S) → (⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ ))
                  , Σ ρ ꞉ ((A : Σ S) → ι A A (≃-refl ⟨ A ⟩))
                  , ({X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t))

 homomorphic : {S : 𝓤 ̇ → 𝓥 ̇ } → SNS S 𝓦
             → (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇
 homomorphic (ι , ρ , θ) = ι

 _≃[_]_ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → SNS S 𝓦 → Σ S → 𝓤 ⊔ 𝓦 ̇
 A ≃[ σ ] B = Σ f ꞉ (⟨ A ⟩ → ⟨ B ⟩)
            , Σ i ꞉ is-equiv f
            , homomorphic σ A B (f , i)

 Id→homEq : {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
          → (A B : Σ S) → (A ＝ B) → (A ≃[ σ ] B)
 Id→homEq (_ , ρ , _) A A (refl {A}) = id , id-is-equiv ⟨ A ⟩ , ρ A

 homomorphism-lemma : {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                      (A B : Σ S) (p : ⟨ A ⟩ ＝ ⟨ B ⟩)
                    →
                      (transport S p (structure A) ＝ structure B)
                    ≃  homomorphic σ A B (idtoeq ⟨ A ⟩ ⟨ B ⟩ p)
 homomorphism-lemma (ι , ρ , θ) (X , s) (X , t) (refl {X}) = γ
  where
   γ : (s ＝ t) ≃ ι (X , s) (X , t) (≃-refl X)
   γ = (canonical-map ι ρ s t , θ s t)

 characterization-of-＝ : is-univalent 𝓤
                       → {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                       → (A B : Σ S)

                       → (A ＝ B) ≃ (A ≃[ σ ] B)
 characterization-of-＝ ua {S} σ A B =
    (A ＝ B)                                                            ≃⟨ i ⟩
    (Σ p ꞉ ⟨ A ⟩ ＝ ⟨ B ⟩ , transport S p (structure A) ＝ structure B) ≃⟨ ii ⟩
    (Σ p ꞉ ⟨ A ⟩ ＝ ⟨ B ⟩ , ι A B (idtoeq ⟨ A ⟩ ⟨ B ⟩ p))               ≃⟨ iii ⟩
    (Σ e ꞉ ⟨ A ⟩ ≃ ⟨ B ⟩ , ι A B e)                                     ≃⟨ iv ⟩
    (A ≃[ σ ] B)                                                        ■
  where
   ι   = homomorphic σ
   i   = Σ-＝-≃
   ii  = Σ-cong (homomorphism-lemma σ A B)
   iii = Σ-change-of-variable (ι A B) (idtoeq ⟨ A ⟩ ⟨ B ⟩) (ua ⟨ A ⟩ ⟨ B ⟩)
   iv  = Σ-assoc

 Id→homEq-is-equiv : (ua : is-univalent 𝓤) {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                   → (A B : Σ S) → is-equiv (Id→homEq σ A B)
 Id→homEq-is-equiv ua {S} σ A B = γ
  where
   h : (A B : Σ S) → Id→homEq σ A B ∼ ⌜ characterization-of-＝ ua σ A B ⌝
   h A A (refl {A}) = refl

   γ : is-equiv (Id→homEq σ A B)
   γ = equiv-closed-under-∼ _ _
        (⌜⌝-is-equiv (characterization-of-＝ ua σ A B))
        (h A B)

 module _ {S : 𝓤 ̇ → 𝓥 ̇ }
          (ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )
          (ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩))
          {X : 𝓤 ̇ }
        where

  canonical-map-charac
   : (s t : S X) (p : s ＝ t)
   → canonical-map ι ρ s t p
   ＝ transport (λ - → ι (X , s) (X , -) (≃-refl X)) p (ρ (X , s))
  canonical-map-charac s t p =
   (yoneda-lemma
    s
    (λ t → ι (X , s) (X , t) (≃-refl X))
    (canonical-map ι ρ s) t p)⁻¹

  when-canonical-map-is-equiv
   : ((s t : S X) → is-equiv (canonical-map ι ρ s t))
   ↔ ((s : S X) → ∃! t ꞉ S X , ι (X , s) (X , t) (≃-refl X))
  when-canonical-map-is-equiv = (λ e s → Yoneda-Theorem-back  s (c s) (e s)) ,
                                (λ φ s → Yoneda-Theorem-forth s (c s) (φ s))
   where
    c = canonical-map ι ρ

  canonical-map-equiv-criterion :
    ((s t : S X) → (s ＝ t) ≃ ι (X , s) (X , t) (≃-refl X))
   → (s t : S X) → is-equiv (canonical-map ι ρ s t)
  canonical-map-equiv-criterion φ s = fiberwise-equiv-criterion'
                                       (λ t → ι (X , s) (X , t) (≃-refl X))
                                       s (φ s) (canonical-map ι ρ s)

  canonical-map-equiv-criterion' :
     ((s t : S X) → ι (X , s) (X , t) (≃-refl X) ◁ (s ＝ t))
    → (s t : S X) → is-equiv (canonical-map ι ρ s t)
  canonical-map-equiv-criterion' φ s = fiberwise-equiv-criterion
                                        (λ t → ι (X , s) (X , t) (≃-refl X))
                                        s (φ s) (canonical-map ι ρ s)

module sip-with-axioms where

 open sip

 [_] : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s) → Σ S
 [ X , s , _ ] = (X , s)

 ⟪_⟫ : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s) → 𝓤 ̇
 ⟪ X , _ , _ ⟫ = X

 add-axioms : {S : 𝓤 ̇ → 𝓥 ̇ }
              (axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ )
            → ((X : 𝓤 ̇ ) (s : S X) → is-prop (axioms X s))
            → SNS S 𝓣
            → SNS (λ X → Σ s ꞉ S X , axioms X s) 𝓣
 add-axioms {𝓤} {𝓥} {𝓦} {𝓣} {S} axioms i (ι , ρ , θ) = ι' , ρ' , θ'
  where
   S' : 𝓤 ̇ → 𝓥 ⊔ 𝓦 ̇
   S' X = Σ s ꞉ S X , axioms X s

   ι' : (A B : Σ S') → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓣 ̇
   ι' A B = ι [ A ] [ B ]

   ρ' : (A : Σ S') → ι' A A (≃-refl ⟨ A ⟩)
   ρ' A = ρ [ A ]

   θ' : {X : 𝓤 ̇ } (s' t' : S' X) → is-equiv (canonical-map ι' ρ' s' t')
   θ' {X} (s , a) (t , b) = γ
    where
     π : S' X → S X
     π (s , _) = s

     j : is-embedding π
     j = pr₁-is-embedding (i X)

     k : {s' t' : S' X} → is-equiv (ap π {s'} {t'})
     k {s'} {t'} = embedding-gives-embedding' π j s' t'

     l : canonical-map ι' ρ' (s , a) (t , b)
       ∼ canonical-map ι ρ s t ∘ ap π {s , a} {t , b}

     l (refl {s , a}) = 𝓻𝓮𝒻𝓵 (ρ (X , s))

     e : is-equiv (canonical-map ι ρ s t ∘ ap π {s , a} {t , b})
     e = ∘-is-equiv k (θ s t)

     γ : is-equiv (canonical-map ι' ρ' (s , a) (t , b))
     γ = equiv-closed-under-∼ _ _ e l

 characterization-of-＝-with-axioms
  : is-univalent 𝓤
  → {S : 𝓤 ̇ → 𝓥 ̇ }
    (σ : SNS S 𝓣)
    (axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ )
  → ((X : 𝓤 ̇ ) (s : S X) → is-prop (axioms X s))
  → (A B : Σ X ꞉ 𝓤 ̇ , Σ s ꞉ S X , axioms X s)
  → (A ＝ B) ≃ ([ A ] ≃[ σ ] [ B ])
 characterization-of-＝-with-axioms ua σ axioms i =
  characterization-of-＝ ua (add-axioms axioms i σ)

module sip-join where

 technical-lemma :

     {X : 𝓤 ̇ } {A : X → X → 𝓥 ̇ }
     {Y : 𝓦 ̇ } {B : Y → Y → 𝓣 ̇ }
     (f : (x₀ x₁ : X) → x₀ ＝ x₁ → A x₀ x₁)
     (g : (y₀ y₁ : Y) → y₀ ＝ y₁ → B y₀ y₁)
   → ((x₀ x₁ : X) → is-equiv (f x₀ x₁))
   → ((y₀ y₁ : Y) → is-equiv (g y₀ y₁))

   → ((x₀ , y₀) (x₁ , y₁) : X × Y) →
   is-equiv (λ (p : (x₀ , y₀) ＝ (x₁ , y₁)) → f x₀ x₁ (ap pr₁ p) ,
                                              g y₀ y₁ (ap pr₂ p))
 technical-lemma {𝓤} {𝓥} {𝓦} {𝓣} {X} {A} {Y} {B} f g i j (x₀ , y₀) = γ
  where
   module _ ((x₁ , y₁) : X × Y) where
    r : (x₀ , y₀) ＝ (x₁ , y₁) → A x₀ x₁ × B y₀ y₁
    r p = f x₀ x₁ (ap pr₁ p) , g y₀ y₁ (ap pr₂ p)

    f' : (a : A x₀ x₁) → x₀ ＝ x₁
    f' = inverse (f x₀ x₁) (i x₀ x₁)

    g' : (b : B y₀ y₁) → y₀ ＝ y₁
    g' = inverse (g y₀ y₁) (j y₀ y₁)

    s : A x₀ x₁ × B y₀ y₁ → (x₀ , y₀) ＝ (x₁ , y₁)
    s (a , b) = to-×-＝ (f' a) (g' b)

    η : (c : A x₀ x₁ × B y₀ y₁) → r (s c) ＝ c
    η (a , b) =
      r (s (a , b))                               ＝⟨refl⟩
      r (to-×-＝  (f' a) (g' b))                  ＝⟨refl⟩
      (f x₀ x₁ (ap pr₁ (to-×-＝ (f' a) (g' b))) ,
       g y₀ y₁ (ap pr₂ (to-×-＝ (f' a) (g' b))))  ＝⟨ ii ⟩
      (f x₀ x₁ (f' a) , g y₀ y₁ (g' b))           ＝⟨ iii ⟩
      a , b                                       ∎
     where
      ii  = ap₂ (λ p q → f x₀ x₁ p , g y₀ y₁ q)
                (ap-pr₁-to-×-＝ (f' a) (g' b))
                (ap-pr₂-to-×-＝ (f' a) (g' b))
      iii = to-×-＝ (inverses-are-sections (f x₀ x₁) (i x₀ x₁) a)
                   (inverses-are-sections (g y₀ y₁) (j y₀ y₁) b)

   γ : (z : X × Y) → is-equiv (r z)
   γ = nats-with-sections-are-equivs (x₀ , y₀) r (λ z → (s z , η z))

 open sip

 ⟪_⟫ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
     → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → 𝓤 ̇
 ⟪ X , s₀ , s₁ ⟫ = X

 [_]₀ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
      → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → Σ S₀
 [ X , s₀ , s₁ ]₀ = (X , s₀)

 [_]₁ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
      → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X) → Σ S₁
 [ X , s₀ , s₁ ]₁ = (X , s₁)

 join : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
      → SNS S₀ 𝓦₀
      → SNS S₁ 𝓦₁
      → SNS (λ X → S₀ X × S₁ X) (𝓦₀ ⊔ 𝓦₁)
 join {𝓤} {𝓥₀} {𝓥₁} {𝓦₀} {𝓦₁} {S₀} {S₁} (ι₀ , ρ₀ , θ₀) (ι₁ , ρ₁ , θ₁) =
  ι , ρ , θ
  where
   S : 𝓤 ̇ → 𝓥₀ ⊔ 𝓥₁ ̇
   S X = S₀ X × S₁ X

   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦₀ ⊔ 𝓦₁ ̇
   ι A B e = ι₀ [ A ]₀ [ B ]₀ e  ×  ι₁ [ A ]₁ [ B ]₁ e

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ A = (ρ₀ [ A ]₀ , ρ₁ [ A ]₁)

   θ : {X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t)
   θ {X} s@(s₀ , s₁) t@(t₀ , t₁) = γ
    where
     c : (p : s ＝ t) → ι₀ (X , s₀) (X , t₀) (≃-refl X)
                      × ι₁ (X , s₁) (X , t₁) (≃-refl X)
     c p = (canonical-map ι₀ ρ₀ s₀ t₀ (ap pr₁ p) ,
            canonical-map ι₁ ρ₁ s₁ t₁ (ap pr₂ p))

     i : is-equiv c
     i = technical-lemma
          (canonical-map ι₀ ρ₀)
          (canonical-map ι₁ ρ₁)
          θ₀ θ₁ s t

     e : canonical-map ι ρ s t ∼ c
     e (refl {s}) = 𝓻𝓮𝒻𝓵 (ρ₀ (X , s₀) , ρ₁ (X , s₁))

     γ : is-equiv (canonical-map ι ρ s t)
     γ = equiv-closed-under-∼ _ _ i e

 _≃⟦_,_⟧_ : {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
          → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)
          → SNS S₀ 𝓦₀
          → SNS S₁ 𝓦₁
          → (Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)
          → 𝓤 ⊔ 𝓦₀ ⊔ 𝓦₁ ̇
 A ≃⟦ σ₀ , σ₁ ⟧ B = Σ f ꞉ (⟪ A ⟫ → ⟪ B ⟫)
                  , Σ i ꞉ is-equiv f , homomorphic σ₀ [ A ]₀ [ B ]₀ (f , i)
                                     × homomorphic σ₁ [ A ]₁ [ B ]₁ (f , i)

 characterization-of-join-＝ : is-univalent 𝓤
                            → {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
                              (σ₀ : SNS S₀ 𝓦₀)  (σ₁ : SNS S₁ 𝓦₁)
                              (A B : Σ X ꞉ 𝓤 ̇ , S₀ X × S₁ X)
                            → (A ＝ B) ≃ (A ≃⟦ σ₀ , σ₁ ⟧ B)
 characterization-of-join-＝ ua σ₀ σ₁ = characterization-of-＝ ua (join σ₀ σ₁)

\end{code}
