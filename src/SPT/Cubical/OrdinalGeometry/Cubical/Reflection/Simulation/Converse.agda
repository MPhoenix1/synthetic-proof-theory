{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Simulation.Converse
  where

-- Simulations of quotient order types read back as initial maps and
-- segments of the presentations, converse to Simulation.
--
-- A simulation g : ord(P) ≼ ord(Q) is read
-- on points through the canonical representatives of Q:
-- x ↦ representative(g [x]). Effectiveness of classes turns equations of
-- classes into equivalences of points, so the lower law of an initial map
-- comes from the lifting of g, without truncation. A bounded simulation
-- ≺ gives a segment whose ceiling represents its bound.

open import Agda.Primitive using (Level)
open import Data.Product using (_,_)

import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Map as Maps
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.OrderType using
  ( Class; Less; orderType
  ; Less-intro
  ; Less-witness
  )
open import SPT.Cubical.OrdinalGeometry.Cubical.Reflection.Representative
  using
  (representative; class; effective)

import Cubical.Foundations.Equiv as Equiv
import Cubical.Foundations.Prelude as Cubical
import Cubical.HITs.SetQuotients as Quotient
import Cubical.Relation.Binary.Order.Woset.Base as Woset
import Cubical.Relation.Binary.Order.Woset.Simulation as Simulation

private
  variable
    ℓ : Level
    P Q : 𝒫 ℓ

  -- Strictness of classes, read on their representatives, and back.
  represent : (Q : 𝒫 ℓ) {a b : Class Q}
    → Less Q a b
    → 𝒫._<_ Q (representative Q a) (representative Q b)
  represent Q {a} {b} s =
    Less-witness Q
      (Cubical.subst2 (Less Q)
        (Cubical.sym (class Q a)) (Cubical.sym (class Q b)) s)

  classify : (Q : 𝒫 ℓ) {a b : Class Q}
    → 𝒫._<_ Q (representative Q a) (representative Q b)
    → Less Q a b
  classify Q {a} {b} r =
    Cubical.subst2 (Less Q) (class Q a) (class Q b)
      (Less-intro Q r)

-- Mathematical shape:
--
--   ord(P) ≼ ord(Q) → Initial P Q,
--   x ↦ representative(g [x]).
--
-- For y < g x, the lifting of g gives a class a with g a = [y]; its
-- representative z has [g z] = g a = [y], so g z ≈ y by effectiveness.
initial : orderType P Simulation.≼ orderType Q
  → Maps.Initial P Q
initial {P = P} {Q = Q} g = record
  { map = to
  ; resp = λ {x} {y} x≈y →
      effective Q
        (class Q (h Quotient.[ x ])
          Cubical.∙ Cubical.cong h (Quotient.eq/ x y x≈y)
          Cubical.∙ Cubical.sym (class Q (h Quotient.[ y ])))
  ; strict = λ {x} {y} x<y →
      represent Q
        (monotone Quotient.[ x ] Quotient.[ y ]
          (Less-intro P x<y))
  ; lower = λ x y y<x′ →
      let fib = lifting Quotient.[ x ] Quotient.[ y ]
            (Cubical.subst (Less Q Quotient.[ y ])
              (class Q (h Quotient.[ x ]))
              (Less-intro Q y<x′))
          a = Cubical.fst (Cubical.fst fib)
      in representative P a
       , effective Q
           (class Q (h Quotient.[ representative P a ])
             Cubical.∙ Cubical.cong h (class P a)
             Cubical.∙ Cubical.snd fib)
  }
  where
  h : Class P → Class Q
  h = Cubical.fst g

  monotone = Cubical.fst (Cubical.snd g)
  lifting = Cubical.snd (Cubical.snd g)

  to : 𝒫.X P → 𝒫.X Q
  to x = representative Q (h Quotient.[ x ])

-- Mathematical shape:
--
--   ord(P) ≺ ord(Q) → Segment P Q,
--
-- for a bound b and e : ord(Q) ↓ b ≃ ord(P).
-- The map sends x to the representative of e⁻¹[x], the ceiling is the
-- representative of b, and a point y below the ceiling is covered by the
-- representative of e([y]).
segment : orderType P Simulation.≺ orderType Q
  → Maps.Segment P Q
segment {P = P} {Q = Q} s = record
  { bound = record
      { to = to
      ; to-≈ = λ {x} {y} x≈y →
          effective Q
            (class Q (point x)
              Cubical.∙ Cubical.cong (λ a → Cubical.fst (back a))
                (Quotient.eq/ x y x≈y)
              Cubical.∙ Cubical.sym (class Q (point y)))
      ; to-< = λ {x} {y} x<y →
          represent Q
            (Equiv.equivFun (order Quotient.[ x ] Quotient.[ y ])
              (Less-intro P x<y))
      ; reflects-< = λ {x} {y} r →
          Less-witness P
            (Equiv.invEq (order Quotient.[ x ] Quotient.[ y ])
              (classify Q r))
      ; ceiling = representative Q b
      ; below = λ x → represent Q (Cubical.snd (back Quotient.[ x ]))
      }
  ; covers = λ y y<c →
      let u = Cubical._,_ Quotient.[ y ]
            (Cubical.subst (Less Q Quotient.[ y ]) (class Q b)
              (Less-intro Q y<c))
          x = representative P (Equiv.equivFun (Cubical.fst e) u)
      in x
       , effective Q
           (class Q (point x)
             Cubical.∙ Cubical.cong (λ a → Cubical.fst (back a))
               (class P (Equiv.equivFun (Cubical.fst e) u))
             Cubical.∙ Cubical.cong Cubical.fst
               (Equiv.retEq (Cubical.fst e) u))
  }
  where
  b : Class Q
  b = Cubical.fst s

  e = Cubical.snd s

  back = Equiv.invEq (Cubical.fst e)

  order = Woset.IsWosetEquiv.pres≺⁻ (Cubical.snd e)

  point : 𝒫.X P → Class Q
  point x = Cubical.fst (back Quotient.[ x ])

  to : 𝒫.X P → 𝒫.X Q
  to x = representative Q (point x)

-- Mathematical shape:
--
--   ord(P) ≃ ord(Q) → P ≃𝒫 Q.
--
-- The reflection reflects equivalence: the Woset equivalence and its
-- inverse are simulations, read back as initial maps in both directions.
equivalence : Woset.WosetEquiv (orderType P) (orderType Q)
  → P Presented.≃𝒫 Q
equivalence e =
  Maps.antisymmetry (initial (Simulation.WosetEquiv→≼ e))
    (initial (Simulation.WosetEquiv→≼ (Woset.invWosetEquiv e)))
