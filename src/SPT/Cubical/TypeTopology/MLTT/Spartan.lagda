Martin Escardo, a long time ago.

Our Spartan (intensional) Martin-Löf type theory has the empty type ∅,
the unit type 𝟙, two-point-type 𝟚, natural numbers ℕ, product types Π,
sum types Σ (and hence binary product types _×_), sum types _+_,
identity types _＝_, and universes 𝓤, 𝓥, 𝓦, ....

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.MLTT.Spartan where

open import SPT.Cubical.TypeTopology.MLTT.Empty           public
open import SPT.Cubical.TypeTopology.MLTT.Unit            public
open import SPT.Cubical.TypeTopology.MLTT.Two             public
open import SPT.Cubical.TypeTopology.MLTT.NaturalNumbers  public
open import SPT.Cubical.TypeTopology.MLTT.Plus            public
open import SPT.Cubical.TypeTopology.MLTT.Pi              public
open import SPT.Cubical.TypeTopology.MLTT.Sigma           public
open import SPT.Cubical.TypeTopology.MLTT.Id              public
open import SPT.Cubical.TypeTopology.MLTT.Universes       public
open import SPT.Cubical.TypeTopology.Notation.General     public

\end{code}
