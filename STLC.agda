module STLC where

open import Data.Bool
open import Data.Integer hiding (suc)
open import Data.Unit
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding (subst)
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
  EInt : ℤ → Term

  EVar : Id → Term

  -- EPlus ELte : Term → Term → Term
  ELam : Type → Term → Term
  EApp : Term → Term → Term

  -- EPair : Term → Term → Term
  -- EFst ESnd : Term → Term

  -- EInl EInr : Term → Type → Term
  -- ECase : Term → Term → Term → Term
--  ELet : Id → Term → Term → Term

weaken : Term -> Term
weaken (EVar x) = EVar (suc x)
weaken EUnit = EUnit
weaken (EInt x) = EInt x
weaken (ELam A m) = ELam A (weaken m)
weaken (EApp f m) = EApp (weaken f) (weaken m)

subst : Term -> Id -> Term -> Term
subst EUnit i n = EUnit
subst (EInt x) i n = EInt x

subst (EVar i) i' n with i Data.Nat.≟ i'
subst (EVar i) i' n | yes refl = n
subst (EVar i) i' n | no _ = EVar i

subst (ELam A m) i n = ELam A (subst m (suc i) (weaken n))
subst (EApp f m) i n = EApp (subst f i n) (subst m i n)

data Context : Set where
  · : Context
  _,_ : Context → Type → Context

-- Typing derivations for terms.
data _⊢_∈_ : Context → Term -> Type → Set where
  UnitTyping : ∀ {Γ} → Γ ⊢ EUnit ∈ `Unit
  IntTyping : ∀ {Γ i} → Γ ⊢ EInt i ∈ `Int

  LastVarTyping : ∀ {Γ A} → ( Γ , A ) ⊢ EVar 0 ∈ A
  NextVarTyping : ∀ {Γ A B n} →
                    Γ         ⊢ EVar n ∈ A →
                    ( Γ , B ) ⊢ EVar (suc n) ∈ A

  ELamTyping : ∀ {Γ A B m} → ( Γ , A ) ⊢ m ∈ B
                           → Γ ⊢ ELam A m ∈ (` A ⇒ B)

  EAppTyping : ∀ {Γ A B f m} → Γ ⊢ f ∈ (` A ⇒ B)
                             → Γ ⊢ m ∈ A
                             → Γ ⊢ EApp f m ∈ B

data Val : Term -> Set where
  UnitVal : Val EUnit
  IntVal : ∀ {i} -> Val (EInt i)
  LamVal : ∀ {A m} -> Val (ELam A m)

data _↦_ : Term -> Term -> Set where
  Beta : ∀ {A n m} -> Val m -> (EApp (ELam A n) m) ↦ subst n 0 m
  AppRight : ∀ {f m m'} -> (m ↦ m')-> (EApp f m) ↦ (EApp f m')
  AppLeft : ∀ {f f' m} -> Val m -> (f ↦ f')-> (EApp f m) ↦ (EApp f' m)

data _↦*_ : Term -> Term -> Set where
  Stop : ∀ {m} -> (m ↦* m)
  Trans : ∀ {m m' m''} -> (m ↦* m') -> (m' ↦ m'') -> (m ↦* m'')

SN : ∀ {A m} -> · ⊢ m ∈ A -> Σ Term (λ v -> m ↦* v × Val v)
SN = {!!}
