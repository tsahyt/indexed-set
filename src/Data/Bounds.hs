{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
module Data.Bounds
(
    Bounds (..),
    collapseBounds
)
where

import GHC.TypeLits
import Data.Constraint
import Data.Constraint.Nat

-- | An existential wrapper around 'Nat' indexed structures of kind @Nat -> * ->
-- *@, such as 'Set', which also provides lower and upper bounds for the
-- existentially quantified index.
--
-- @Bounds l h x a@ therefore provides proof that @l@ is a lower bound on the
-- index of @x@, and @h@ is an upper bound on it.
--
-- Pattern matching on the @Bounds@ constructor brings a 'KnownNat' @n@
-- constraint into scope, as well as @l <= n@ and @n <= h@.
data Bounds (x :: Nat -> * -> *) (l :: Nat) (h :: Nat) a where
    Bounds :: (l <= n, n <= h, KnownNat n) => x n a -> Bounds x l h a

-- | Given a 'Bounds' with two equal bounds, collapse it to the contained
-- structure. In other words, given that @l <= k <= h@, we get a proof that @l =
-- k = h@ and therefore, the existentially quantified index can be extracted.
collapseBounds :: forall n f a. KnownNat n => Bounds f n n a -> f n a
collapseBounds (Bounds (x :: f k a)) = x \\ leEq @n @k
{-# INLINABLE collapseBounds #-}
