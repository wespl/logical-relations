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

data Context : Set where
  · : Context
  _,_ : Context → Type → Context

ctxSize : Context -> ℕ
ctxSize · = 0
ctxSize (Γ , A) = suc (ctxSize Γ)


weaken : Term -> Term
weaken (EVar x) = EVar (suc x)
weaken EUnit = EUnit
weaken (EInt x) = EInt x
weaken (ELam A m) = ELam A (weaken m)
weaken (EApp f m) = EApp (weaken f) (weaken m)

data UntypedSubst : Context -> Context -> Set where
  · : ∀ {Γ} -> UntypedSubst Γ ·
  _,_ : ∀ {Γ Δ A} -> UntypedSubst Γ Δ → Term → UntypedSubst Γ (Δ , A)

-- data Subst : Context -> Context -> Set where
--   · : ∀ {Γ} -> Subst Γ ·
--   _,_ : ∀ {Γ Δ A} -> Subst Γ Δ → TypedTerm Γ A → Subst Γ (Δ , A)

weakenSubst : ∀ {Γ Δ A} -> UntypedSubst Γ Δ -> UntypedSubst (Γ , A) Δ
weakenSubst {Δ = ·} · = ·
weakenSubst {Δ = Δ , x} (s , e) = weakenSubst s , weaken e

applySubst : ∀ {Γ Δ} -> Term -> UntypedSubst Γ Δ -> Term
applySubst EUnit ctx = EUnit
applySubst (EInt x) ctx = EInt x
applySubst (EVar zero) (rest , e') = e'
applySubst (EVar (suc x)) (rest , e') = applySubst (EVar x) rest
applySubst (EVar n) · = EVar n -- should never arise with well-formed e
applySubst (ELam t e) ctx = ELam t (applySubst e (_,_ {A = t} (weakenSubst {A = t} ctx) (EVar zero)))
-- when we push the substitution under the binder, we need to add [x/x] in the substitution
applySubst (EApp e e₁) ctx = EApp (applySubst e ctx) (applySubst e₁ ctx)


--subst e x e' = e[e'/x]
-- This is broken.
subst : Term -> Id -> Term -> Term
subst e x e' =  {!!}
--subst EUnit i n = EUnit
--subst (EInt x) i n = EInt x

--subst (EVar i) i' n with i Data.Nat.≟ i'
--subst (EVar i) i' n | yes refl = n
--subst (EVar i) i' n | no _ = EVar i

--subst (ELam A m) i n = ELam A (subst m (suc i) (weaken n))
--subst (EApp f m) i n = EApp (subst f i n) (subst m i n)

-- Typing derivations for terms.
data _⊢_⦂_ : Context → Term -> Type → Set where
  UnitTyping : ∀ {Γ} → Γ ⊢ EUnit ⦂ `Unit
  IntTyping : ∀ {Γ i} → Γ ⊢ EInt i ⦂ `Int

  LastVarTyping : ∀ {Γ A} → ( Γ , A ) ⊢ EVar 0 ⦂ A
  NextVarTyping : ∀ {Γ A B n} →
                    Γ         ⊢ EVar n ⦂ A →
                    ( Γ , B ) ⊢ EVar (suc n) ⦂ A

  ELamTyping : ∀ {Γ A B m} → ( Γ , A ) ⊢ m ⦂ B
                           → Γ ⊢ ELam A m ⦂ (` A ⇒ B)

  EAppTyping : ∀ {Γ A B f m} → Γ ⊢ f ⦂ (` A ⇒ B)
                             → Γ ⊢ m ⦂ A
                             → Γ ⊢ EApp f m ⦂ B

data Val : Term -> Set where
  UnitVal : Val EUnit
  IntVal : ∀ {i} -> Val (EInt i)
  LamVal : ∀ {A m} -> Val (ELam A m)

data _↦_ : Term -> Term -> Set where
  Beta : ∀ {A n m} -> Val m -> (EApp (ELam A n) m) ↦ subst n 0 m
  AppRight : ∀ {f m m'} -> (m ↦ m') -> (EApp f m) ↦ (EApp f m')
  -- AppLeft : ∀ {f f' m} -> Val m -> (f ↦ f')-> (EApp f m) ↦ (EApp f' m)
  AppLeft : ∀ {f f' m} -> (f ↦ f') -> (EApp f m) ↦ (EApp f' m)

data _↦*_ : Term -> Term -> Set where
  Stop : ∀ {m} -> (m ↦* m)
  Trans : ∀ {m m' m''} -> (m ↦ m') -> (m' ↦* m'') -> (m ↦* m'')

HT : Type -> Term -> Set
HT `Unit e = e ↦* EUnit
HT `Int e = Σ ℤ (λ v -> e ↦* (EInt v))
HT (` A ⇒ B) f = ∀ {e} -> HT A e -> HT B (EApp f e)
HT (` A × B) e = {!!}
HT (` A ⊎ B) e = {!!}


goodSubst : (Γ : Context) -> UntypedSubst · Γ -> Set
goodSubst .· · = ⊤
goodSubst .(_ , _) (_,_ {Δ = Δ} {A = A} subst e) = HT A e × goodSubst Δ subst

OHT : Context -> Type -> Term -> Set
OHT Γ τ e = ∀ {γ} -> (goodSubst Γ γ) -> HT τ (applySubst e γ)

converseEval : ∀ {e e' t} -> e ↦ e' -> HT t e' -> HT t e
converseEval {t = `Int} s (z , ss) = z , (Trans s ss)
converseEval {t = `Unit} s ht = Trans s ht
converseEval {t = ` t ⇒ t₁} s ht hte₁ = {!!}
converseEval {t = ` t × t₁} s ht = {!!}
converseEval {t = ` t ⊎ t₁} s ht = {!!}

wtOHT : ∀ {Γ τ e} -> Γ ⊢ e ⦂ τ -> OHT Γ τ e
wtOHT  UnitTyping s = Stop
wtOHT {e = e} (IntTyping {i = i})  subst = i , Stop
wtOHT {τ = τ} LastVarTyping {γ , x} (ht , _) = ht
wtOHT {τ = τ} (NextVarTyping {B = B} {n} tyderiv) {γ , x} (xGood , restGood) = wtOHT tyderiv restGood
wtOHT {Γ} (ELamTyping {A = A} {B} {m} tyderiv) {γ} isGood {e} ht = let ih = wtOHT tyderiv in
                                                                   let bodyht = ih {γ = (γ , e)} (ht , isGood) in {!!}
  -- ELamTyping : ∀ {Γ A B m} → ( Γ , A ) ⊢ m ⦂ B
  --                          → Γ ⊢ ELam A m ⦂ (` A ⇒ B)
wtOHT (EAppTyping mderiv fderiv) {γ} isGood = ((wtOHT mderiv) isGood) ((wtOHT fderiv) isGood)

SN : ∀ {A m} → · ⊢ m ⦂ A -> Σ Term (λ v -> m ↦* v × Val v)
SN UnitTyping = EUnit , (Stop , UnitVal)
SN (IntTyping {i = i}) = EInt i , Stop , IntVal
SN (ELamTyping {A = A} {m = m} lamderiv) = ELam A m , (Stop , LamVal)
SN (EAppTyping fderiv mderiv) = {!!}
