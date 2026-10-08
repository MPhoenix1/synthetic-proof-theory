One-element type properties.

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.MLTT.Unit-Properties where

open import SPT.Cubical.TypeTopology.MLTT.Unit
open import SPT.Cubical.TypeTopology.MLTT.Empty
open import SPT.Cubical.TypeTopology.MLTT.Id
open import SPT.Cubical.TypeTopology.MLTT.Negation

𝟙-all-⋆ : (x : 𝟙 {𝓤}) → x ＝ ⋆
𝟙-all-⋆ {𝓤} ⋆ = refl {𝓤}
𝟙-is-not-𝟘 : 𝟙 ≠ 𝟘
𝟙-is-not-𝟘 p = transport (λ X → X) p ⋆

\end{code}
