module STLC where

open import Data.Bool
open import Data.Integer
open import Data.Unit
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Data.String
open import Data.Nat.Show
open import Data.List
open import Data.Empty
open import Function

Id : Set
Id = ℕ

data Type : Set where
  `Int  : Type
  `Unit : Type
  `_⇒_  : Type → Type → Type
  `_×_  : Type → Type → Type
  `_⊎_ : Type → Type → Type

-- Abstract syntax tree.
-- These can fail type checking.
data Term : Set where
  EUnit : Term
  EVar : Id → Term
  ENat : ℤ → Term
  EPlus ELte EApp EPair : Term → Term → Term
  EFst ESnd : Term → Term
  ECase : Term → Term → Term → Term
  ELet : Id → Term → Term → Term
  ELam : Id → Type → Term → Term
  EInl EInr : Term → Type → Term

Context : Set
Context = {!!}

-- Typing derivations for terms.
data _⊢_ : Context → Term -> Type → Set where
