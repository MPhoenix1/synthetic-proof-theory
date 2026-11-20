{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel where

-- Results that need Agda's two-level type theory (--two-level): strict
-- identification and the outer types it lives in. SPT's Foundation and its
-- other owners are one-level; what uses SSet outside LCTT is here. This
-- module is an index; each module is imported by name where it is used.
--
--   Coherence     strict identification _≐_ (application, transport,
--                 composition, passage to identity), the outer unit type,
--                 and classes of identifications closed under path
--                 induction: every identification, and those induced by
--                 strict ones
--   Empty         the fibrant empty type eliminates into every outer type
--   Mahlo         the strict Mahlo rule for a Tarski family, every
--                 decoding law a strict identification in context
--   Mahlo.Branches
--                 branches respect strict identification of families
--   Mahlo.StepAlgebra
--                 a labelled algebra of the Mahlo step with classified
--                 carriers gives the strict rule
--   Mahlo.StepAlgebra.Discriminator
--                 induction–recursion gives the strict ambient Mahlo rule
--   Mahlo.Displayed
--                 the strict Mahlo rule for displayed families: base codes
--                 and fiber codes over them
--   Mahlo.Displayed.Branches
--                 base and fiber points carried along strictly identified
--                 split families, and their branches
--   Mahlo.Displayed.StepAlgebra
--                 a labelled display algebra gives the strict displayed
--                 rule
--   Mahlo.Displayed.StepAlgebra.Discriminator
--                 induction–recursion gives fiber codes over each ambient
--                 step code, and with them the strict displayed rule

import SPT.TwoLevel.Coherence
import SPT.TwoLevel.Empty
import SPT.TwoLevel.Mahlo
import SPT.TwoLevel.Mahlo.Branches
import SPT.TwoLevel.Mahlo.StepAlgebra
import SPT.TwoLevel.Mahlo.StepAlgebra.Discriminator
import SPT.TwoLevel.Mahlo.Displayed
import SPT.TwoLevel.Mahlo.Displayed.Branches
import SPT.TwoLevel.Mahlo.Displayed.StepAlgebra
import SPT.TwoLevel.Mahlo.Displayed.StepAlgebra.Discriminator
