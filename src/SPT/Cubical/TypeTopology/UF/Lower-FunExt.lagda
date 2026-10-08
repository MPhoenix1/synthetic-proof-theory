Martin Escardo, 13th January 2021.

Interface to code from my MGS 2019 lecture notes.

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.UF.Lower-FunExt where

open import SPT.Cubical.TypeTopology.MLTT.Spartan
open import SPT.Cubical.TypeTopology.UF.Base
open import SPT.Cubical.TypeTopology.UF.Equiv
open import SPT.Cubical.TypeTopology.UF.FunExt

open import SPT.Cubical.TypeTopology.MGS.TypeTopology-Interface

import SPT.Cubical.TypeTopology.MGS.Equivalences
import SPT.Cubical.TypeTopology.MGS.FunExt-from-Univalence
import SPT.Cubical.TypeTopology.MGS.Universe-Lifting

abstract

  lower-DN-funext : ∀ 𝓦 𝓣 → DN-funext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → DN-funext 𝓤 𝓥
  lower-DN-funext {𝓤} {𝓥} 𝓦 𝓣 fe = SPT.Cubical.TypeTopology.MGS.Universe-Lifting.lower-dfunext 𝓦 𝓣 𝓤 𝓥 fe

  DN-funext-gives-funext : {𝓤 𝓥 : Universe} → DN-funext 𝓤 𝓥 → funext 𝓤 𝓥
  DN-funext-gives-funext dnfe {X} {A} f g = γ
   where
    h : f ＝ g → f ∼ g
    h = SPT.Cubical.TypeTopology.MGS.FunExt-from-Univalence.happly f g

    a : is-equiv h
    a = MGS-equivs-are-equivs h (SPT.Cubical.TypeTopology.MGS.FunExt-from-Univalence.dfunext-gives-hfunext dnfe f g)

    b : is-equiv (happly' f g)
    b = equiv-closed-under-∼ h (happly' f g) a (happly'-is-MGS-happly f g)

    c :  SPT.Cubical.TypeTopology.MGS.Equivalences.is-equiv (happly' f g)
    c = equivs-are-MGS-equivs (happly' f g) b

    γ : is-equiv (happly' f g)
    γ = MGS-equivs-are-equivs (happly' f g) c

  lower-funext : ∀ 𝓦 𝓣 → funext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → funext 𝓤 𝓥
  lower-funext {𝓤} {𝓥} 𝓦 𝓣 fe = DN-funext-gives-funext
                                   (lower-DN-funext 𝓦 𝓣 (dfunext fe))

  lower-fun-ext : ∀ {𝓦} 𝓣 → funext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → funext 𝓤 𝓥
  lower-fun-ext {𝓤} {𝓥} {𝓦} 𝓣 fe = DN-funext-gives-funext
                                      (lower-DN-funext 𝓦 𝓣 (dfunext fe))

\end{code}
