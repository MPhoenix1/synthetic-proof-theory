Martin Escardo. 13th January 2021

This is to be be able to call the MGS lectures notes code from
TypeTopology. This will grow as the need arises.

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.MGS.TypeTopology-Interface where

open import SPT.Cubical.TypeTopology.MLTT.Spartan
open import SPT.Cubical.TypeTopology.UF.Base
open import SPT.Cubical.TypeTopology.UF.Equiv

import SPT.Cubical.TypeTopology.MGS.Equivalences
import SPT.Cubical.TypeTopology.MGS.FunExt-from-Univalence

MGS-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → SPT.Cubical.TypeTopology.MGS.Equivalences.is-equiv f
                      → is-equiv f
MGS-equivs-are-equivs = vv-equivs-are-equivs

equivs-are-MGS-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f
                      → SPT.Cubical.TypeTopology.MGS.Equivalences.is-equiv f
equivs-are-MGS-equivs = equivs-are-vv-equivs

happly'-is-MGS-happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A)
                      → happly' f g ∼ SPT.Cubical.TypeTopology.MGS.FunExt-from-Univalence.happly f g
happly'-is-MGS-happly f g refl = refl

\end{code}
