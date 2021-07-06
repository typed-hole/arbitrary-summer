{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE StandaloneKindSignatures #-}
module Data.Sums
  ( In (..)
  , Sum (..)
  , foldSum
  , emptySumIsVoid
  ) where

import Data.Kind (Type)
import Data.Void (Void, absurd)
import Data.Functor.Contravariant (Op(Op))

-- | Proof that the some type variable is present in a type level list
type In :: k -> [k] -> Type
data In x xs where
  -- | Direct proof that x is the head of the list x:xs
  Here :: x `In` (x ': xs)
  -- | Recursive proof that if x is in the list xs, then x is also in
  --   "xs with extra elements"
  There :: (x `In` xs) -> x `In` (y ': xs)

-- | Generalized sum type. Like an @Either@ with arbitrarily many constructors
type Sum :: [Type] -> Type
data Sum types where
  -- | To inject a value of type @t@ into @Sum ts@, provide a proof that
  --   @t@ exists in the list @ts@
  MkSum :: t `In` ts -> t -> Sum ts

-- | If you can give a list of functions that map the types in @ts@ to @r@,
--   you can turn a value of type @Sum ts@ into a value of type @r@.
--   Corresponds to @Data.Either.either@
--
-- >>> foldSum (Op even :. Op null :. Nil) (MkSum (There Here) "hi" :: Sum '[Int, String])
-- False
foldSum :: FList (Op result) types -> Sum types -> result
foldSum fs s@(MkSum p x) = case p of
  Here -> case fs of
    Op f :. _   -> f x
  There p' -> case fs of
    _    :. fs' -> foldSum fs' $ MkSum p' x

-- | It's impossible to construct a value of an empty sum. This would mean that the
--   injected value has a type which is contained in an empty list, but an empty list
--   doesn't contain anything.
emptySumIsVoid :: Sum '[] -> void
emptySumIsVoid (MkSum p _x) = case p of

-- | @FList@ is a heterogenous list plus a type constructor which is "@fmap@:ed" over
--   the type level list.
--   e.g. @HList Maybe '[Int, Bool, Char]@ is a list containing a @Maybe Int@, a
--   @Maybe Bool@, and a @Maybe Char@
type FList :: (k -> Type) -> [k] -> Type
data FList f xs where
  -- | Empty list
  Nil :: FList f '[]
  -- | Append an item to the front of a list
  (:.) :: f x -> FList f xs -> FList f (x ': xs)
infixr :.
