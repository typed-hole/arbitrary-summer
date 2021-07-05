{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Data.Sums
  ( In (..)
  , Sum (..)
  ) where

import Data.Kind (Type)
import Data.Text (Text)
import Data.Void (absurd)
import qualified Data.Text as T

-- | Proof that the some type variable is present in a type level list
data In :: k -> [k] -> Type where
  -- | Direct proof that x is the head of the list x:xs
  Here :: x `In` (x ': xs)
  -- | Recursive proof that if x is in the list xs, then x is also in
  --   "xs with extra elements"
  There :: (x `In` xs) -> x `In` (y ': xs)

-- | Generalized sum type. Like an @Either@ with arbitrarily many constructors
data Sum :: [Type] -> Type where
  -- | To inject a value of type @t@ into @Sum ts@, provide a proof that
  --   @t@ exists in the list @ts@
  MkSum :: t `In` ts -> t -> Sum ts

in_0 :: (forall void. void) -> Sum '[]
in_0 = absurd

-- | The "first" injection function. Corresponds to @Left@ for @Either@
in_1 :: a -> Sum (a ': ts)
in_1 = MkSum Here

-- | The "second" injection function. Corresponds to @Right@ for @Either@
in_2 :: b -> Sum (a ': b ': ts)
in_2 = MkSum (There Here)

-- | The "third" injection function.
in_3 :: c -> Sum (a ': b ': c ': ts)
in_3 = MkSum (There . There $ Here)

-- | If you can give a list of functions that map the types in @ts@ to @r@,
--   you can turn a value of @Sum ts@ into a value of type @r@.
--   Corresponds to @Data.Either.either@
sumElim :: FList ((:<-) r) ts -> Sum ts -> r
sumElim fs s@(MkSum p x) = case fs of
  Nil -> emptySumIsVoid s
  From f :. fs' -> case p of
    Here -> f x
    There p' -> sumElim fs' (MkSum p' x)

-- | It's impossible to construct a value of an empty sum. This would mean that the
--   injected value has a type which is contained in an empty list, but an empty list
--   doesn't contain anything.
emptySumIsVoid :: Sum '[] -> void
emptySumIsVoid (MkSum p _x) = case p of

-- | @a :<- b@ is a function from @b@ to @a@
newtype a :<- b = From (b -> a)

-- | This is a heterogenous list plus a type constructor which is "@fmap@:ed" over
--   the type level list.
--   e.g. @HList Maybe '[Int, Bool, Char]@ is a list containing a @Maybe Int@, a
--   @Maybe Bool@, and a @Maybe Char@
data FList :: (k -> Type) -> [k] -> Type where
  -- | Empty list
  Nil :: FList f '[]
  -- | Append an item to the front of a list
  (:.) :: f x -> FList f xs -> FList f (x ': xs)
infixr :.

example :: Sum '[Int, Bool, Char] -> Text
example = sumElim $ From show' :. From show' :. From show' :. Nil
  where
    show' :: forall a. Show a => a -> Text
    show' = T.pack . show
