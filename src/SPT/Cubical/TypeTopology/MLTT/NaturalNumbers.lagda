Natural numbers

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.MLTT.NaturalNumbers where

open import SPT.Cubical.TypeTopology.MLTT.Universes
open import SPT.Cubical.TypeTopology.MLTT.Natural-Numbers-Type public

rec : {X : 𝓤 ̇ } → X → (X → X) → (ℕ → X)
rec x f zero = x
rec x f (succ n) = f(rec x f n)

_^_ : {X : 𝓤 ̇ } → (X → X) → ℕ → (X → X)
(f ^ n) x = rec x f n

ℕ-induction : {A : ℕ → 𝓤 ̇ } → A 0 → ((k : ℕ) → A k → A(succ k)) → (n : ℕ) → A n
ℕ-induction base step 0 = base
ℕ-induction base step (succ n) = step n (ℕ-induction base step n)

\end{code}
