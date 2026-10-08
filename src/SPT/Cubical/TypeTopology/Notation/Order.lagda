Martin Escardo 31st December 2021

Type-class for notation for strict orders.

\begin{code}

{-# OPTIONS --safe --without-K --cubical-compatible #-}

module SPT.Cubical.TypeTopology.Notation.Order where

open import SPT.Cubical.TypeTopology.MLTT.Spartan

record Strict-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇ where
 field
   _<_ : X → Y → 𝓦 ̇

 _≮_ : X → Y → 𝓦 ̇
 _>_ _≯_ : Y → X → 𝓦 ̇

 x ≮ y = ¬(x < y)
 y > x = x < y
 y ≯ x = ¬ (y > x)

 infix 30 _<_
 infix 30 _>_
 infix 30 _≮_
 infix 30 _≯_

open Strict-Order {{...}} public

record Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇ where
 field
   _≤_ : X → Y → 𝓦 ̇

 _≰_ : X → Y → 𝓦 ̇
 _≥_ _≱_ : Y → X → 𝓦 ̇

 x ≰ y = ¬(x ≤ y)
 y ≥ x = x ≤ y
 y ≱ x = ¬(y ≥ x)

 infix 30 _≤_
 infix 30 _≥_
 infix 30 _≰_
 infix 30 _≱_


open Order {{...}} public

record Strict-Square-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇ where
 field
   _⊏_ : X → Y → 𝓦 ̇

 _⊐_ : Y → X → 𝓦 ̇
 x ⊐ y = y ⊏ x

 infix 30 _⊏_
 infix 30 _⊐_

open Strict-Square-Order {{...}} public

record Square-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇ where
 field
   _⊑_ : X → Y → 𝓦 ̇

 _⊒_ : Y → X → 𝓦 ̇
 x ⊒ y = y ⊑ x

 infix 30 _⊑_
 infix 30 _⊒_

open Square-Order {{...}} public

record Strict-Curly-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇ where
 field
   _≺_ : X → Y → 𝓦 ̇

 _≻_ : Y → X → 𝓦 ̇
 x ≻ y = y ≺ x

 infix 30 _≺_
 infix 30 _≻_

open Strict-Curly-Order {{...}} public

record Curly-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇ where
 field
   _≼_ : X → Y → 𝓦 ̇

 _≽_ : Y → X → 𝓦 ̇
 x ≽ y = y ≼ x

 infix 30 _≼_
 infix 30 _≽_

open Curly-Order {{...}} public

record Strict-Order-Chain {𝓤} {𝓥} {𝓦} {𝓣} {𝓧 : Universe}
 (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (Z : 𝓦 ̇ )
 (_<₁_ : X → Y → 𝓣 ̇ )
 (_<₂_ : Y → Z → 𝓧 ̇ ) :  (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓧)⁺ ̇ where
 field
  _<_<_ : X → Y → Z → 𝓣 ⊔ 𝓧 ̇

 infix 30 _<_<_

open Strict-Order-Chain {{...}} public

record Order-Chain {𝓤} {𝓥} {𝓦} {𝓣} {𝓧 : Universe}
 (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (Z : 𝓦 ̇ )
 (_≤₁_ : X → Y → 𝓣 ̇ )
 (_≤₂_ : Y → Z → 𝓧 ̇ ) :  (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓧)⁺ ̇ where
 field
  _≤_≤_ : X → Y → Z → 𝓣 ⊔ 𝓧 ̇

 infix 30 _≤_≤_

open Order-Chain {{...}} public

\end{code}

Lane Biocini, 10 October 2023

Define a general notation for reasoning chains

\begin{code}
record Reflexive-Order {𝓤} (X : 𝓤 ̇ )
 (_R_ : X → X → 𝓤 ̇ ) : 𝓤 ̇ where
 field
  _▨ : (x : X) → x R x

 infix 1 _▨

open Reflexive-Order {{...}} public

record Reasoning-Chain {𝓤} {𝓥} {𝓦} {𝓣} {𝓧 : Universe}
 (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (Z : 𝓦 ̇ )
 (_R₁_ : X → Y → 𝓦 ̇ )
 (_R₂_ : Y → Z → 𝓣 ̇ )
 (_R₃_ : X → Z → 𝓧 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓧)⁺ ̇ where
 field
  _⸴_⊢_ : (x : X) {y : Y} {z : Z} → x R₁ y → y R₂ z → x R₃ z

 infixr 0 _⸴_⊢_

open Reasoning-Chain {{...}} public

\end{code}
