module Cubical.Data.Prod.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Prod.Base
open import Cubical.Data.Sigma renaming (_×_ to _×Σ_) hiding (prodIso ; toProdIso ; curryIso)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

-- Swapping is an equivalence

×≡ : {a b : A × B} → proj₁ a ≡ proj₁ b → proj₂ a ≡ proj₂ b → a ≡ b
×≡ {a = (_ , _)} {b = (_ , _)} id1 id2 i = (id1 i) , (id2 i)

swap : A × B → B × A
swap (x , y) = (y , x)

swap-invol : (xy : A × B) → swap (swap xy) ≡ xy
swap-invol (_ , _) = refl

isEquivSwap : (A : Type ℓ) (B : Type ℓ') → isEquiv (λ (xy : A × B) → swap xy)
isEquivSwap A B = isoToIsEquiv (iso swap swap swap-invol swap-invol)

swapEquiv : (A : Type ℓ) (B : Type ℓ') → A × B ≃ B × A
swapEquiv A B = (swap , isEquivSwap A B)

swapEq : (A : Type ℓ) (B : Type ℓ') → A × B ≡ B × A
swapEq A B = ua (swapEquiv A B)

private
  open import Cubical.Data.Nat

  -- As × is defined as a datatype this computes as expected
  -- (i.e. "C-c C-n test1" reduces to (2 , 1)). If × is implemented
  -- using Sigma this would be "transp (λ i → swapEq ℕ ℕ i) i0 (1 , 2)"
  test : ℕ × ℕ
  test = transp (λ i → swapEq ℕ ℕ i) i0 (1 , 2)

  testrefl : test ≡ (2 , 1)
  testrefl = refl

  test' : ℕ ×Σ ℕ
  test' = transp (λ i → ua (Σ-swap-≃ {A = ℕ} {A' = ℕ}) i) i0 (1 , 2)

  test'refl : test' ≡ (2 , 1)
  test'refl = refl

-- equivalence between the sigma-based definition and the inductive one
A×B≃A×ΣB : A × B ≃ A ×Σ B
A×B≃A×ΣB = isoToEquiv (iso (λ { (a , b) → (a , b)})
                          (λ { (a , b) → (a , b)})
                          (λ _ → refl)
                          (λ { (a , b) → refl }))

A×B≡A×ΣB : A × B ≡ A ×Σ B
A×B≡A×ΣB = ua A×B≃A×ΣB

-- truncation for products
isOfHLevelProd : (n : HLevel) → isOfHLevel n A → isOfHLevel n B → isOfHLevel n (A × B)
isOfHLevelProd {A = A} {B = B} n h1 h2 =
  let h : isOfHLevel n (A ×Σ B)
      h = isOfHLevelΣ n h1 (λ _ → h2)
  in transport (λ i → isOfHLevel n (A×B≡A×ΣB {A = A} {B = B} (~ i))) h


×-≃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
    → A ≃ C → B ≃ D → A × B ≃ C × D
×-≃ {A = A} {B = B} {C = C} {D = D} f g = isoToEquiv (iso φ ψ η ε)
   where
    φ : A × B → C × D
    φ (a , b) = equivFun f a , equivFun g b

    ψ : C × D → A × B
    ψ (c , d) = equivFun (invEquiv f) c , equivFun (invEquiv g) d

    η : section φ ψ
    η (c , d) i = secEq f c i , secEq g d i

    ε : retract φ ψ
    ε (a , b) i = retEq f a i , retEq g b i


{- Some simple ismorphisms -}

prodIso : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
       → Iso A C
       → Iso B D
       → Iso (A × B) (C × D)
Iso.fun (prodIso iAC iBD) (a , b) = (Iso.fun iAC a) , Iso.fun iBD b
Iso.inv (prodIso iAC iBD) (c , d) = (Iso.inv iAC c) , Iso.inv iBD d
Iso.sec (prodIso iAC iBD) (c , d) = ×≡ (Iso.sec iAC c) (Iso.sec iBD d)
Iso.ret (prodIso iAC iBD) (a , b) = ×≡ (Iso.ret iAC a) (Iso.ret iBD b)

toProdIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         → Iso (A → B × C) ((A → B) × (A → C))
Iso.fun toProdIso = λ f → (λ a → proj₁ (f a)) , (λ a → proj₂ (f a))
Iso.inv toProdIso (f , g) = λ a → (f a) , (g a)
Iso.sec toProdIso (f , g) = refl
Iso.ret toProdIso b = funExt λ a → sym (×-η _)

curryIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         → Iso (A × B → C) (A → B → C)
Iso.fun curryIso f a b = f (a , b)
Iso.inv curryIso f (a , b) = f a b
Iso.sec curryIso a = refl
Iso.ret curryIso f = funExt λ {(a , b) → refl}

fiber-map-× : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
    (f : B → C) (a : A) (c : C)
  → Iso (fiber f c) (fiber (map-× (idfun A) f) (a , c))
fiber-map-× f a c .Iso.fun z .fst .fst = a
fiber-map-× f a c .Iso.fun z .fst .snd = z .fst
fiber-map-× f a c .Iso.fun z .snd = ≡-× refl (z .snd)
fiber-map-× f a c .Iso.inv z .fst = z .fst .snd
fiber-map-× f a c .Iso.inv z .snd = cong snd (z .snd)
fiber-map-× f a c .Iso.sec ((az , bz) , e) j .fst .fst = cong fst e (~ j)
fiber-map-× f a c .Iso.sec ((az , bz) , e) j .fst .snd = bz
fiber-map-× f a c .Iso.sec ((az , bz) , e) j .snd k .fst = cong fst e (k ∨ ~ j)
fiber-map-× f a c .Iso.sec ((az , bz) , e) j .snd k .snd = cong snd e k
fiber-map-× f a c .Iso.ret z = refl
