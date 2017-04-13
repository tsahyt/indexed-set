{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
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

    -- * Construction
    empty,
    singleton,
    insert,

    -- * Combine
    union,
    difference,
    (\\),
    intersection,
    
    -- * Filter
    -- TODO

    -- * Map
    -- TODO: map
    unsafeMapMonotonic,

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
    withSet
)
where

import Control.DeepSeq
import Data.Coerce
import Data.Proxy
import Data.Data
import Data.Constraint.Nat
import Data.Typeable
import GHC.TypeLits
import qualified Data.Set as S
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as N
import qualified Data.Constraint as C

import Unsafe.Coerce

import Prelude hiding (null, map, foldr, foldl)

newtype Set (n :: Nat) a = ISet (S.Set a)
    deriving (Show, Eq, Ord, Foldable, Data, Typeable, NFData)

null :: Set n a -> Bool
null = S.null . coerce

size :: forall a n. KnownNat n => Set n a -> Int
size _ = fromIntegral $ natVal (Proxy :: Proxy n)

size' :: forall n a. Set n a -> Proxy n
size' _ = Proxy

member :: Ord a => a -> Set n a -> Bool
member x s = S.member x (coerce s)

notMember :: Ord a => a -> Set n a -> Bool
notMember x s = S.notMember x (coerce s)

lookupLT :: Ord a => a -> Set n a -> Maybe a
lookupLT x s = S.lookupLT x (coerce s)

lookupGT :: Ord a => a -> Set n a -> Maybe a
lookupGT x s = S.lookupGT x (coerce s)

lookupLE :: Ord a => a -> Set n a -> Maybe a
lookupLE x s = S.lookupLE x (coerce s)

lookupGE :: Ord a => a -> Set n a -> Maybe a
lookupGE x s = S.lookupGE x (coerce s)

isSubsetOf :: Ord a => Set n a -> Set (n + m) a -> Bool
isSubsetOf a b = S.isSubsetOf (coerce a) (coerce b)

isProperSubsetOf :: Ord a => Set n a -> Set (n + m + 1) a -> Bool
isProperSubsetOf a b = S.isProperSubsetOf (coerce a) (coerce b)

empty :: Set 0 a
empty = ISet S.empty

singleton :: a -> Set 1 a
singleton x = ISet (S.singleton x)

insert :: Ord a => a -> Set n a -> Either (Set n a) (Set (n + 1) a)
insert x (ISet s) 
    | S.member x s = Left $ ISet (S.insert x s)
    | otherwise    = Right $ ISet (S.insert x s)

delete :: Ord a => a -> Set (n + 1) a -> Either (Set (n + 1) a) (Set n a)
delete x old@(ISet s)
    | S.member x s = Right $ ISet (S.delete x s)
    | otherwise    = Left old

data Bounds (l :: Nat) (h :: Nat) (x :: Nat -> * -> *) a where
    Bounds :: (l <= n, n <= h, KnownNat n) => x n a -> Bounds l h x a

collapseBounds :: forall n f a. KnownNat n => Bounds n n f a -> f n a
collapseBounds (Bounds (x :: f k a)) = x C.\\ leEq @n @k

-- Deeply evil
axiom :: forall a b. C.Dict (a ~ b)
axiom = unsafeCoerce (C.Dict :: C.Dict (a ~ a))

axiomLe :: forall a b. C.Dict (a <= b)
axiomLe = axiom

union :: forall n m a. Ord a 
    => Set n a -> Set m a -> Bounds (Max n m) (n + m) Set a
union a b = case someNatVal (fromIntegral (S.size r)) of
    Just (SomeNat (Proxy :: Proxy k)) ->
        let r' = ISet r :: Set k a
            l  = axiomLe @(Max n m) @k
            h  = axiomLe @k @(n + m)
         in C.withDict l (C.withDict h (Bounds r'))
    where r = S.union (coerce a) (coerce b)

difference :: forall n m a. (Ord a, m <= n) 
    => Set n a -> Set m a -> Bounds (n - m) n Set a
difference a b = case someNatVal (fromIntegral (S.size r)) of
    Just (SomeNat (Proxy :: Proxy k)) ->
        let r' = ISet r :: Set k a
            l  = axiomLe @(n - m) @k
            h  = axiomLe @k @n
         in C.withDict l (C.withDict h (Bounds r'))
    where r = S.difference (coerce a) (coerce b)

infixl 9 \\

(\\) :: (Ord a, m <= n) => Set n a -> Set m a -> Bounds (n - m) n Set a
a \\ b = difference a b

intersection :: forall n m a. Ord a 
    => Set n a -> Set m a -> Bounds 0 (Min n m) Set a
intersection a b = case someNatVal (fromIntegral (S.size r)) of
    Just (SomeNat (Proxy :: Proxy k)) ->
        let r' = ISet r :: Set k a
            l  = axiomLe @0 @k
            h  = axiomLe @k @(Min n m)
         in C.withDict l (C.withDict h (Bounds r'))
    where r = S.intersection (coerce a) (coerce b)

unsafeMapMonotonic :: (a -> b) -> Set n a -> Set n b
unsafeMapMonotonic f (ISet x) = ISet (S.mapMonotonic f x)

foldr :: (a -> b -> b) -> b -> Set n a -> b
foldr f z s = S.foldr f z (coerce s)

foldl :: (a -> b -> a) -> a -> Set n b -> a
foldl f z s = S.foldl f z (coerce s)

foldr' :: (a -> b -> b) -> b -> Set n a -> b
foldr' f z s = S.foldr' f z (coerce s)

foldl' :: (a -> b -> a) -> a -> Set n b -> a
foldl' f z s = S.foldl' f z (coerce s)

findMin :: Set (n + 1) a -> a
findMin x = S.findMin (coerce x)

findMax :: Set (n + 1) a -> a
findMax x = S.findMax (coerce x)

deleteMin :: Set (n + 1) a -> Set n a
deleteMin x = ISet $ S.deleteMin (coerce x)

deleteMax :: Set (n + 1) a -> Set n a
deleteMax x = ISet $ S.deleteMax (coerce x)

maxView :: Set (n + 1) a -> (a, Set n a)
maxView x = case S.maxView (coerce x) of
    Nothing -> error "impossible"
    Just x' -> fmap ISet x'

minView :: Set (n + 1) a -> (a, Set n a)
minView x = case S.minView (coerce x) of
    Nothing -> error "impossible"
    Just x' -> fmap ISet x'

elems :: Set n a -> [a]
elems = S.elems . coerce

elemsNE :: Set (n + 1) a -> N.NonEmpty a
elemsNE = N.fromList . elems

toList :: Set n a -> [a]
toList = S.toList . coerce

toListNE :: Set (n + 1) a -> N.NonEmpty a
toListNE = N.fromList . toList

fromList :: forall n a. (KnownNat n, Ord a) => [a] -> Maybe (Set n a)
fromList xs
    | length xs == n = Just $ ISet (S.fromList xs)
    | otherwise = Nothing
    where n = fromIntegral $ natVal (Proxy :: Proxy n)

withList :: forall a r. Ord a 
    => [a] -> (forall n. KnownNat n => Set n a -> r) -> r
withList xs f = case someNatVal (fromIntegral $ S.size s) of
    Just (SomeNat (Proxy :: Proxy n)) -> let s' = ISet s :: Set n a in f s'
    where s = S.fromList xs

toAscList :: Set n a -> [a]
toAscList = S.toAscList . coerce

toAscListNE :: Set (n + 1) a -> N.NonEmpty a
toAscListNE = N.fromList . toAscList

toDescList :: Set n a -> [a]
toDescList = S.toDescList . coerce

toDescListNE :: Set (n + 1) a -> N.NonEmpty a
toDescListNE = N.fromList . toDescList

fromSet :: forall n a. KnownNat n => S.Set a -> Maybe (Set n a)
fromSet s 
    | S.size s == n = Just (ISet s)
    | otherwise = Nothing      
    where n = fromIntegral $ natVal (Proxy :: Proxy n)

withSet :: forall a r. S.Set a -> (forall n. KnownNat n => Set n a -> r) -> r
withSet s f = case someNatVal (fromIntegral $ S.size s) of
    Just (SomeNat (Proxy :: Proxy n)) -> let s' = ISet s :: Set n a in f s'
