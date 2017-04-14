-- | A set structure indexed by cardinality. This module provides a relatively
-- lightweight wrapper around "Data.Set" from the @containers@ package, adding
-- a cardinality index to the type.
-- 
-- In some places this allows making functions total. In other places, we need
-- to resort to existential quantification (e.g. 'union') because the exact
-- cardinality cannot be deduced purely from the input cardinalities. In those
-- cases, the 'Bounds' type is used to at least provide lower and upper bounds.
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Data.Set.Indexed
(
    Set,
    
    -- * Query
    null,
    size,
    size',
    member,
    notMember,
    isSubsetOf,
    isProperSubsetOf,
    isProperSubsetOf',

    -- * Cardinality
    witnessNull,
    exactCardinality,
    exactBounds,

    -- * Construction
    empty,
    singleton,
    insert,
    insert',
    delete,
    delete',

    -- * Combine
    union,
    difference,
    (\\),
    intersection,
    
    -- * Filter
    filter,
    partition,
    split,

    -- * Indexed
    lookupIndex,
    elemAt,
    deleteAt,

    -- * Map
    map,

    -- * Folds
    foldr,
    foldl,

    -- ** Strict Folds
    foldr',
    foldl',

    -- * Min/Max
    findMin,
    findMax,
    deleteMin,
    deleteMax,
    minView,
    maxView,

    -- * Conversion
    elems,
    elemsNE,
    toList,
    toListNE,
    fromList,
    withList,

    -- ** Ordered list
    toAscList,
    toAscListNE,
    toDescList,
    toDescListNE,

    -- ** Unindexed Sets
    fromSet,
    withSet,

    -- * Bounds
    Bounds (..),
    collapseBounds
)
where

import Control.DeepSeq
import Data.Bounds
import Data.Coerce
import Data.Constraint.Nat
import Data.Data
import Data.Finite
import Data.Proxy
import Data.Typeable
import GHC.TypeLits

import qualified Data.Set as S
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as N
import qualified Data.Constraint as C

import Unsafe.Coerce

import Prelude hiding (null, map, foldr, foldl, filter)

-- | A set of values @a@, indexed by cardinality.
newtype Set (n :: Nat) a = ISet (S.Set a)
    deriving (Eq, Ord, Foldable, Data, Typeable, NFData)

instance Show a => Show (Set n a) where
    show (ISet s) = show s

-- | /O(1)/. Provide type level proof that a given set is empty.
witnessNull :: Set n a -> Maybe (Set 0 a)
witnessNull x = exactCardinality Proxy x
{-# INLINE witnessNull #-}

-- | /O(1)/. Safely try to cast a set of some cardinality to a set of some exact
-- given cardinality. If the given set does not match the given cardinality,
-- 'Nothing' is returned.
exactCardinality :: forall n m a. KnownNat n 
    => Proxy n -> Set m a -> Maybe (Set n a)
exactCardinality n (ISet s) = do
    SomeNat (Proxy :: Proxy k) <- someNatVal (fromIntegral (S.size s))
    Refl <- sameNat n (Proxy @k)
    return (ISet s)
{-# INLINABLE exactCardinality #-}

-- | /O(1)/. Extract a 'Set' from 'Bounds' by guessing its cardinality.
--
-- > exactBounds n (Bounds s) = exactCardinality n s
--
exactBounds :: KnownNat n => Proxy n -> Bounds Set l h a -> Maybe (Set n a)
exactBounds n (Bounds s) = exactCardinality n s
{-# INLINE exactBounds #-}

-- | /O(1)/. Is this the empty set?
null :: Set n a -> Bool
null = S.null . coerce
{-# INLINE null #-}

-- | /O(1)/. The number of elements in the set.
size :: forall a n. Set n a -> Int
size s = S.size (coerce s)
{-# INLINE size #-}

-- | /O(1)/. The number of elements in the set, returned as a 'Proxy'
size' :: forall n a. Set n a -> Proxy n
size' _ = Proxy
{-# INLINE size' #-}

-- | /O(log n)/. Is the element in the set?
member :: Ord a => a -> Set n a -> Bool
member x s = S.member x (coerce s)
{-# INLINE member #-}

-- | /O(log n)/. Is the element not in the set?
notMember :: Ord a => a -> Set n a -> Bool
notMember x s = S.notMember x (coerce s)
{-# INLINE notMember #-}

-- | /O(log n)/. Find largest element smaller than the given one.
--
-- > lookupLT 3 (fromList [3, 5]) == Nothing
-- > lookupLT 5 (fromList [3, 5]) == Just 3
lookupLT :: Ord a => a -> Set n a -> Maybe a
lookupLT x s = S.lookupLT x (coerce s)
{-# INLINE lookupLT #-}

-- | /O(log n)/. Find smallest element greater than the given one.
--
-- > lookupGT 4 (fromList [3, 5]) == Just 5
-- > lookupGT 5 (fromList [3, 5]) == Nothing
lookupGT :: Ord a => a -> Set n a -> Maybe a
lookupGT x s = S.lookupGT x (coerce s)
{-# INLINE lookupGT #-}

-- | /O(log n)/. Find largest element smaller or equal to the given one.
--
-- > lookupLE 2 (fromList [3, 5]) == Nothing
-- > lookupLE 4 (fromList [3, 5]) == Just 3
-- > lookupLE 5 (fromList [3, 5]) == Just 5
lookupLE :: Ord a => a -> Set n a -> Maybe a
lookupLE x s = S.lookupLE x (coerce s)
{-# INLINE lookupLE #-}

-- | /O(log n)/. Find smallest element greater or equal to the given one.
--
-- > lookupGE 3 (fromList [3, 5]) == Just 3
-- > lookupGE 4 (fromList [3, 5]) == Just 5
-- > lookupGE 6 (fromList [3, 5]) == Nothing
lookupGE :: Ord a => a -> Set n a -> Maybe a
lookupGE x s = S.lookupGE x (coerce s)
{-# INLINE lookupGE #-}

-- | /O(n+m)/. Is this a subset?
-- @(s1 `isSubsetOf` s2)@ tells whether @s1@ is a subset of @s2@.
--
-- Note that the types allow the second set to be of greater cardinality.
-- However, @m ~ 0@ is valid as well.
isSubsetOf :: Ord a => Set n a -> Set (n + m) a -> Bool
isSubsetOf a b = S.isSubsetOf (coerce a) (coerce b)
{-# INLINE isSubsetOf #-}

-- | /O(n+m)/. Is this a proper subset? (ie. a subset but not equal). This
-- version requires the second argument to be non-empty.
isProperSubsetOf :: Ord a => Set n a -> Set (n + m + 1) a -> Bool
isProperSubsetOf a b = S.isProperSubsetOf (coerce a) (coerce b)
{-# INLINE isProperSubsetOf #-}

-- | /O(n+m)/. Like 'isProperSubsetOf', but not requiring the second argument to
-- be non-empty.
isProperSubsetOf' :: Ord a => Set n a -> Set (n + m) a -> Bool
isProperSubsetOf' a b = S.isProperSubsetOf (coerce a) (coerce b)
{-# INLINE isProperSubsetOf' #-}

-- | /O(1)/. The empty set.
empty :: Set 0 a
empty = ISet S.empty
{-# INLINE empty #-}

-- | /O(1)/. Create a singleton set.
singleton :: a -> Set 1 a
singleton x = ISet (S.singleton x)
{-# INLINE singleton #-}

-- | /O(log n)/. Insert an element in a set.
-- If the set already contains an element equal to the given value,
-- 'Left' is returned where the value is replaced with the given value.
-- Otherwise 'Right' is returned.
insert :: Ord a => a -> Set n a -> Either (Set n a) (Set (n + 1) a)
insert x (ISet s) 
    | S.member x s = Left $ ISet (S.insert x s)
    | otherwise    = Right $ ISet (S.insert x s)
{-# INLINABLE insert #-}

-- | Like 'insert', but will return 'Nothing' when the element is already in the
-- set.
insert' :: Ord a => a -> Set n a -> Maybe (Set (n + 1) a )
insert' x s = either (const Nothing) Just (insert x s)

-- | /O(log n)/. Delete an element from a set. If the element is not in the set,
-- the old set is returned in 'Left'. 'Right' contains the set with the element
-- removed.
delete :: Ord a => a -> Set (n + 1) a -> Either (Set (n + 1) a) (Set n a)
delete x old@(ISet s)
    | S.member x s = Right $ ISet (S.delete x s)
    | otherwise    = Left old
{-# INLINABLE delete #-}

-- | Like 'delete', but will return 'Nothing' when the element was not in the
-- set.
delete' :: Ord a => a -> Set (n + 1) a -> Maybe (Set n a)
delete' x s = either (const Nothing) Just (delete x s)

unsafeMkBounds :: forall a l h. S.Set a -> Bounds Set l h a
unsafeMkBounds r = case someNatVal (fromIntegral (S.size r)) of
    Just (SomeNat (Proxy :: Proxy k)) ->
        let r' = ISet r :: Set k a
            l  = axiomLe @l @k
            h  = axiomLe @k @h
         in C.withDict l (C.withDict h (Bounds r'))
{-# INLINE unsafeMkBounds #-}

-- Deeply evil
axiom :: forall a b. C.Dict (a ~ b)
axiom = unsafeCoerce (C.Dict :: C.Dict (a ~ a))

axiomLe :: forall a b. C.Dict (a <= b)
axiomLe = axiom

-- | /O(m*log(n\/m + 1)), m <= n/. The union of two sets, preferring the first
-- set when equal elements are encountered.
union :: forall n m a. Ord a 
    => Set n a -> Set m a -> Bounds Set (Max n m) (n + m) a
union a b = unsafeMkBounds (S.union (coerce a) (coerce b))
{-# INLINE union #-}

-- | /O(m*log(n\/m + 1)), m <= n/. Difference of two sets.
difference :: forall n m a. (Ord a, m <= n) 
    => Set n a -> Set m a -> Bounds Set (n - m) n a
difference a b = unsafeMkBounds (S.difference (coerce a) (coerce b))
{-# INLINE difference #-}

infixl 9 \\

-- | /O(m*log(n\/m+1)), m <= n/. See 'difference'.
(\\) :: (Ord a, m <= n) => Set n a -> Set m a -> Bounds Set (n - m) n a
a \\ b = difference a b
{-# INLINE (\\) #-}

-- | /O(m*log(n\/m + 1)), m <= n/. The intersection of two sets.  Elements of
-- the result come from the first set.
intersection :: forall n m a. Ord a 
    => Set n a -> Set m a -> Bounds Set 0 (Min n m) a
intersection a b = unsafeMkBounds (S.intersection (coerce a) (coerce b))
{-# INLINE intersection #-}

-- | /O(n)/. Filter all elements that satisfy the predicate.
filter :: (a -> Bool) -> Set n a -> Bounds Set 0 n a
filter p s = unsafeMkBounds (S.filter p (coerce s))
{-# INLINE filter #-}

-- | /O(n)/. Partition the set into two sets, one with all elements that satisfy
-- the predicate and one with all elements that don't satisfy the predicate.
-- See also 'split'.
partition :: (a -> Bool) -> Set n a -> (Bounds Set 0 n a, Bounds Set 0 n a)
partition p s = 
    let (l,r) = S.partition p (coerce s)
     in (unsafeMkBounds l, unsafeMkBounds r)
{-# INLINABLE partition #-}

-- | /O(log n)/. The expression (@'split' x set@) is a pair @(set1,set2)@
-- where @set1@ comprises the elements of @set@ less than @x@ and @set2@
-- comprises the elements of @set@ greater than @x@.
split :: Ord a => a -> Set n a -> (Bounds Set 0 n a, Bounds Set 0 n a)
split x s =
    let (l,r) = S.split x (coerce s)
     in (unsafeMkBounds l, unsafeMkBounds r)
{-# INLINABLE split #-}

-- | /O(log n)/. Performs a 'split' but also returns whether the pivot
-- element was found in the original set in the form of a 'Maybe'.
splitMember :: Ord a 
    => a -> Set n a -> Maybe (Bounds Set 0 n a, Bounds Set 0 n a)
splitMember x s = case S.splitMember x (coerce s) of
     (_,False,_) -> Nothing
     (l,_,r) -> Just (unsafeMkBounds l, unsafeMkBounds r)
{-# INLINABLE splitMember #-}

-- | /O(log n)/. Lookup the /index/ of an element, which is its zero-based index
-- in the sorted sequence of elements. The index is a number from /0/ up to, but
-- not including, the 'size' of the set.
lookupIndex :: (KnownNat n, Ord a) => a -> Set n a -> Maybe (Finite n)
lookupIndex x s = do
    i <- S.lookupIndex x (coerce s)
    packFinite (fromIntegral i)
{-# INLINABLE lookupIndex #-}

-- | /O(log n)/. Retrieve an element by its /index/, i.e. by its zero-based
-- index in the sorted sequence of elements. If the /index/ is out of range
-- (less than zero, greater or equal to 'size' of the set), 'error' is called.
elemAt :: Finite n -> Set n a -> a
elemAt i s = let i' = fromIntegral (getFinite i) in S.elemAt i' (coerce s)
{-# INLINE elemAt #-}

-- | /O(log n)/. Delete the element at /index/, i.e. by its zero-based index in
-- the sorted sequence of elements. If the /index/ is out of range (less than
-- zero, greater or equal to 'size' of the set), 'error' is called.
deleteAt :: Ord a => Finite (n + 1) -> Set (n + 1) a -> Set n a
deleteAt i s = 
    let i' = fromIntegral (getFinite i)
        s' = S.deleteAt i' (coerce s)
     in ISet s'
{-# INLINABLE deleteAt #-}

-- | /O(n*log n)/.  @'map' f s@ is the set obtained by applying @f@ to each
-- element of @s@. The result may be smaller than the original.
map :: Ord b => (a -> b) -> Set n a -> Bounds Set 0 n b
map f s = unsafeMkBounds (S.map f (coerce s))
{-# INLINE map #-}

-- | /O(n)/. Fold the elements in the set using the given right-associative
-- binary operator, such that @'foldr' f z == 'Prelude.foldr' f z .
-- 'toAscList'@.
foldr :: (a -> b -> b) -> b -> Set n a -> b
foldr f z s = S.foldr f z (coerce s)
{-# INLINE foldr #-}

-- | /O(n)/. Fold the elements in the set using the given left-associative
-- binary operator, such that @'foldl' f z == 'Prelude.foldl' f z .
-- 'toAscList'@.
--
-- For example,
--
-- > toDescList set = foldl (flip (:)) [] set
foldl :: (a -> b -> a) -> a -> Set n b -> a
foldl f z s = S.foldl f z (coerce s)
{-# INLINE foldl #-}

-- | /O(n)/. A strict version of 'foldr'. Each application of the operator is
-- evaluated before using the result in the next application. This
-- function is strict in the starting value.
foldr' :: (a -> b -> b) -> b -> Set n a -> b
foldr' f z s = S.foldr' f z (coerce s)
{-# INLINE foldr' #-}

-- | /O(n)/. A strict version of 'foldl'. Each application of the operator is
-- evaluated before using the result in the next application. This
-- function is strict in the starting value.
foldl' :: (a -> b -> a) -> a -> Set n b -> a
foldl' f z s = S.foldl' f z (coerce s)
{-# INLINE foldl' #-}

-- | /O(log n)/. The minimal element of a non-empty set.
findMin :: Set (n + 1) a -> a
findMin x = S.findMin (coerce x)
{-# INLINE findMin #-}

-- | /O(log n)/. The maximal element of a non-empty set.
findMax :: Set (n + 1) a -> a
findMax x = S.findMax (coerce x)
{-# INLINE findMax #-}

-- | /O(log n)/. Delete the minimal element. Returns an empty set if the set is
-- empty.
deleteMin :: Set (n + 1) a -> Set n a
deleteMin x = ISet $ S.deleteMin (coerce x)
{-# INLINE deleteMin #-}

-- | /O(log n)/. Delete the maximal element. Returns an empty set if the set is
-- empty.
deleteMax :: Set (n + 1) a -> Set n a
deleteMax x = ISet $ S.deleteMax (coerce x)
{-# INLINE deleteMax #-}

-- | /O(log n)/. Retrieves the maximal key of the set, and the set stripped of
-- that element.
maxView :: Set (n + 1) a -> (a, Set n a)
maxView x = case S.maxView (coerce x) of Just x' -> fmap ISet x'
{-# INLINE maxView #-}

-- | /O(log n)/. Retrieves the minimal key of the set, and the set stripped of
-- that element.
minView :: Set (n + 1) a -> (a, Set n a)
minView x = case S.minView (coerce x) of Just x' -> fmap ISet x'
{-# INLINE minView #-}

-- | /O(n)/. An alias of 'toAscList'. The elements of a set in ascending order.
-- Subject to list fusion.
elems :: Set n a -> [a]
elems = S.elems . coerce
{-# INLINE elems #-}

-- | /O(n)/. An alias of 'toAscListNE'. The elements of a set in ascending
-- order.
elemsNE :: Set (n + 1) a -> N.NonEmpty a
elemsNE = N.fromList . elems
{-# INLINE elemsNE #-}

-- | /O(n)/. Convert the set to a list of elements. Subject to list fusion.
toList :: Set n a -> [a]
toList = S.toList . coerce
{-# INLINE toList #-}

-- | /O(n)/. Convert the set to a non-empty list of elements.
toListNE :: Set (n + 1) a -> N.NonEmpty a
toListNE = N.fromList . toList
{-# INLINE toListNE #-}

-- | /O(n*log n)/. Create a set from a list of elements.
--
-- If the elements are ordered, a linear-time implementation is used,
-- with the performance equal to 'fromDistinctAscList'.
fromList :: forall n a. (KnownNat n, Ord a) => [a] -> Maybe (Set n a)
fromList xs
    | S.size s == n = Just $ ISet s
    | otherwise = Nothing
    where n = fromIntegral $ natVal (Proxy :: Proxy n)
          s = S.fromList xs
{-# INLINABLE fromList #-}

-- | Perform a function on 'Set' on a list.
withList :: forall a r. Ord a 
    => [a] -> (forall n. KnownNat n => Set n a -> r) -> r
withList xs f = case someNatVal (fromIntegral $ S.size s) of
    Just (SomeNat (Proxy :: Proxy n)) -> let s' = ISet s :: Set n a in f s'
    where s = S.fromList xs
{-# INLINE withList #-}

-- | /O(n)/. Convert the set to an ascending list of elements. Subject to list
-- fusion.
toAscList :: Set n a -> [a]
toAscList = S.toAscList . coerce
{-# INLINE toAscList #-}

-- | /O(n)/. Convert the set to an ascending non-empty list of elements.
toAscListNE :: Set (n + 1) a -> N.NonEmpty a
toAscListNE = N.fromList . toAscList
{-# INLINE toAscListNE #-}

-- | /O(n)/. Convert the set to a descending list of elements. Subject to list
-- fusion.
toDescList :: Set n a -> [a]
toDescList = S.toDescList . coerce
{-# INLINE toDescList #-}

-- | /O(n)/. Convert the set to a descending non-empty list of elements.
toDescListNE :: Set (n + 1) a -> N.NonEmpty a
toDescListNE = N.fromList . toDescList
{-# INLINE toDescListNE #-}

-- | /O(1)/. Convert an ordinary 'S.Set' to a cardinality indexed 'Set' of a
-- given size. Will return 'Nothing' if the sizes do not match.
fromSet :: forall n a. KnownNat n => S.Set a -> Maybe (Set n a)
fromSet s 
    | S.size s == n = Just (ISet s)
    | otherwise = Nothing      
    where n = fromIntegral $ natVal (Proxy :: Proxy n)
{-# INLINABLE fromSet #-}

-- | Perform a function on 'Set' on an ordinary 'S.Set'.
withSet :: forall a r. S.Set a -> (forall n. KnownNat n => Set n a -> r) -> r
withSet s f = case someNatVal (fromIntegral $ S.size s) of
    Just (SomeNat (Proxy :: Proxy n)) -> let s' = ISet s :: Set n a in f s'
{-# INLINE withSet #-}
