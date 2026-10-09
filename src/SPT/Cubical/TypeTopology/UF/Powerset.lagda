Martin Escardo, 5th September 2018, 27th September 2023.

The contents of this file has been generalized in terms of universe levels
and has been moved to SPT.Cubical.TypeTopology.UF.Powerset-MultiUniverse.

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.UF.Powerset where

open import SPT.Cubical.TypeTopology.MLTT.Spartan
open import SPT.Cubical.TypeTopology.UF.Powerset-MultiUniverse
  renaming (𝓟 to 𝓟') public

𝓟 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓟 {𝓤} X = 𝓟' {𝓤} X

\end{code}
