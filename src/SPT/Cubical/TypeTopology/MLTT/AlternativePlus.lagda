Alternative of _+_:

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.MLTT.AlternativePlus where

open import SPT.Cubical.TypeTopology.MLTT.Universes
open import SPT.Cubical.TypeTopology.MLTT.Two
open import SPT.Cubical.TypeTopology.MLTT.Sigma

_+'_ : 𝓤 ̇ → 𝓤 ̇ → 𝓤 ̇
X₀ +' X₁ = Σ i ꞉ 𝟚 , 𝟚-cases X₀ X₁ i

\end{code}
