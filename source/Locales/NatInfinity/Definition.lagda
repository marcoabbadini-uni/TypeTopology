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

open import CoNaturals.GenericConvergentSequence
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Powerset-MultiUniverse
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

\begin{code}

is-open : 𝓟 {𝓤₀} ℕ∞ → 𝓤₀  ̇
is-open P =  ∞ ∈ P → ∃ n ꞉ ℕ , (ℕ-to-ℕ∞ n) ∈ P

Open : 𝓤₁  ̇
Open = Σ P ꞉ (𝓟 {𝓤₀} ℕ∞) , is-open P

\end{code}
