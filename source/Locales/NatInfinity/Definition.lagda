---
title:        Definition of ℕ∞ as a locale
author:       Marco Abbadini
date-started: 2024-03-06
---


\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import MLTT.List hiding ([_])

module Locales.NatInfinity.Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import CoNaturals.GenericConvergentSequence hiding (max)
open import Locales.Frame pt fe
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt
open import Naturals.Order

open AllCombinators pt fe
open PropositionalTruncation pt
open PropositionalSubsetInclusionNotation fe

\end{code}

\begin{code}



is-open : 𝓟 {𝓤₀} ℕ∞ → 𝓤₀  ̇
is-open P =  ∞ ∈ P → ∃ n ꞉ ℕ , ((m : ℕ) → (n ≤ℕ m) → (ℕ-to-ℕ∞ m) ∈ P)

being-open-is-prop : (P : 𝓟 {𝓤₀} ℕ∞) → is-prop (is-open P)
being-open-is-prop P = Π-is-prop fe (λ n → ∥∥-is-prop)


Open : 𝓤₁  ̇
Open = Σ P ꞉ (𝓟 {𝓤₀} ℕ∞) , is-open P

_⊆ᵖ_ : Open → Open → Ω 𝓤₀
(P , u) ⊆ᵖ (Q , v) = P ⊆ₚ Q


⊆ᵖ-is-reflexive : is-reflexive _⊆ᵖ_ holds
⊆ᵖ-is-reflexive (P , _) n p = p

⊆ᵖ-is-transitive : is-transitive _⊆ᵖ_ holds
⊆ᵖ-is-transitive (P₀ , u₀) (P₁ , u₁) (P₂ , u₂) p q = ⊆-trans P₀ P₁ P₂ p  q

⊆ᵖ-is-preorder : is-preorder _⊆ᵖ_ holds
⊆ᵖ-is-preorder = (⊆ᵖ-is-reflexive , ⊆ᵖ-is-transitive)

full∞ : Open
full∞ = full , λ x → ∣ 0 , (λ m x₁ → ⋆) ∣

full∞-is-top : (P : Open) → (P ⊆ᵖ full∞) holds
full∞-is-top (P , u) _ _ = ⋆


open Meets _⊆ᵖ_

_∩∞_ : Open → Open → Open
(P , u) ∩∞ (Q , v) = P ∩ Q , †
 where
  † : is-open (P ∩ Q)
  † (p , q) = {!!} -- ∥∥-rec ∃-is-prop β ?
   --where
   -- β : Σ m ꞉ ℕ , P (ℕ-to-ℕ∞ m) holds → ∃ (λ n → (P ∩ Q) (ℕ-to-ℕ∞ n) holds)
   -- β (m , p₀) = ∥∥-rec ∃-is-prop γ {!!}
    -- where
     -- γ : Σ n ꞉ ℕ , Q (ℕ-to-ℕ∞ n) holds → ∃ (λ n → (P ∩ Q) (ℕ-to-ℕ∞ n) holds)
      --γ (n , q₀) = ∣ max m n , {!!} , {!!} ∣

∩-gives-glb : (((P , u) , (Q , v)) : Open × Open) → (((P , u) ∩∞ (Q , v)) is-glb-of ((P , u) , (Q , v))) holds
∩-gives-glb (P , Q) = {!!} --((λ _ → pr₁) , (λ _ → pr₂))
                     , λ (_ , φ , ψ) x r → φ x r , ψ x r




--⊆-refl' : {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X) → A ⊆ A
--⊆-refl' A x = id



\end{code}
