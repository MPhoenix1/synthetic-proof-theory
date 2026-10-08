\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.MLTT.Unit-Type where

open import SPT.Cubical.TypeTopology.MLTT.Universes public

data 𝟙 {𝓤} : 𝓤 ̇ where
 ⋆ : 𝟙

\end{code}
