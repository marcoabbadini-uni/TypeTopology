Martin Escardo
15 February 2021.

In collaboration with Marc Bezem, Thierry Coquand and Peter Dybjer.

This module has the technical lemmas necessary to prove the
following:

  For any universe 𝓤, there is a group in the successor universe 𝓤⁺
  which is not isomorphic to any group in 𝓤.

Of course, in the other direction, any group in 𝓤 has an isomorphic
copy in 𝓤⁺, so the above says that there are strictly more groups in
𝓤⁺ than in 𝓤.

In the module BuraliForti.lagda we use the group freely generated by
the (large but locally small) type of ordinals for that purpose.

We work in a spartan Martin-Löf type theory, with the assumption that
propositional truncations exist and that the univalence axiom
holds. No other features of HoTT/UF are needed.

In particular, quotients, which we use to construct free groups, are
constructed using propositional truncation and function extensionality
and propositional extensionality in the module UF.Quotient. This
construction of quotients increases the universe level by one (but its
universal property eliminates into any universe), so that the group
freely generated by a type A in a universe 𝓤 lives in the next
universe 𝓤⁺ (but again its universal property eliminates into any
universe).

In this file with work with a given locally small type A : 𝓤⁺ for an
arbitrary universe 𝓤 and we show that the free group constructed in
the module FreeGroup.lagda, which lives in the universe 𝓤⁺⁺, has a
copy in the same universe 𝓤⁺ where A lives, provided A is locally
small (meaning that its identity types, which live in 𝓤⁺, have
equivalent copies in 𝓤). Moreover, we show that if the group freely
generated by A has a copy in the universe 𝓤, then A itself must have a
copy in 𝓤.  We then apply this in the module BuraliForti.lagda by
taking A to be the type of ordinals in the universe 𝓤, which doesn't
have a copy in 𝓤, from which we conclude that the free group also
doesn't have a copy in 𝓤.

For that purpose, we need to know, in particular, that the inclusion
of generators is injective, which is proved in the module
FreeGroup.lagda. But this is is not enough: for example, the unique
map P → 𝟙 is an embedding if P is a proposition, and the terminal
type 𝟙 is of course small, but P doesn't need to be small - cf. work
with Tom de Jong on size matters https://arxiv.org/abs/2102.08812,
from which we borrow other techniques in the development below.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.Univalence

module Groups.FreeGroupOfLargeLocallySmallSet
        (pt : propositional-truncations-exist)
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt
open import UF.Subsingletons
open import UF.Base
open import UF.Embeddings
open import UF.Equiv hiding (_≅_)
open import UF.EquivalenceExamples
open import UF.Size

open import MLTT.List
open import Groups.SRTclosure
open import Groups.Groups
open import Groups.FreeGroup

fe : Fun-Ext
fe = Univalence-gives-Fun-Ext ua

pe : Prop-Ext
pe = Univalence-gives-Prop-Ext ua

open import UF.Large-Quotient pt fe pe
open FreeGroupInterface pt fe pe

\end{code}

The last three assumptions in the following module parameters are a
slight weakening of the local smallness condition on the type A.

\begin{code}

module resize-free-group
         {𝓤        : Universe}
         (A        : 𝓤 ⁺ ̇)
         (A-is-set : is-set A)
         (_≡₀_     : A → A → 𝓤 ̇ )
         (refl₀    : (a : A) → a ≡₀ a)
         (from-≡₀  : (a b : A) → a ≡₀ b → a ≡ b)
       where

 open free-group-construction A

 private
  𝓤⁺  = 𝓤 ⁺
  𝓤⁺⁺ = 𝓤⁺ ⁺

\end{code}

Our free group is constructed as a quotient of a set of words FA by a
certain equivalence relation _∾_ : FA → FA → 𝓤⁺. To reduce the size of
the quotient, we reduce the size of (propositional) values of this
equivalence relation using the assumed relation _≡₀_ and functions
refl₀ and from-≡₀.

At this point, in order to understand the following constructions, it
is necessary to first understand the constructions in the module
FreeGroup.lagda, because here we resize down several of the
constructions performed in that file, exploiting the (weakened version
of the) local smalless of the type A.

\begin{code}

 _≡[X]_ : X → X → 𝓤 ̇
 (m , a) ≡[X] (n , b) = (m ≡ n) × (a ≡₀ b)

 from-≡[X] : {x y : X} → x ≡[X] y → x ≡ y
 from-≡[X] {m , a} {n , b} (p , q) = to-×-≡ p (from-≡₀ a b q)

 to-≡[X] : {x y : X} → x ≡ y → x ≡[X] y
 to-≡[X] {m , a} {m , a} refl = refl , refl₀ a

 _≡[FA]_ : FA → FA → 𝓤 ̇
 []      ≡[FA] []      = 𝟙
 []      ≡[FA] (y ∷ t) = 𝟘
 (x ∷ s) ≡[FA] []      = 𝟘
 (x ∷ s) ≡[FA] (y ∷ t) = (x ≡[X] y) × (s ≡[FA] t)

 from-≡[FA] : {s t : FA} → s ≡[FA] t → s ≡ t
 from-≡[FA] {[]}    {[]}    e       = refl
 from-≡[FA] {x ∷ s} {y ∷ t} (p , q) = ap₂ _∷_ (from-≡[X] p) (from-≡[FA] q)

 to-≡[FA] : {s t : FA} → s ≡ t → s ≡[FA] t
 to-≡[FA] {[]} {[]}       p = ⋆
 to-≡[FA] {x ∷ s} {y ∷ t} p = to-≡[X]  (equal-heads p) ,
                              to-≡[FA] (equal-tails p)

 _◗_ : FA → FA → 𝓤 ̇
 []          ◗ t = 𝟘
 (x ∷ [])    ◗ t = 𝟘
 (x ∷ y ∷ s) ◗ t = (y ≡[X] (x ⁻)) × (s ≡[FA] t)

 _▶_ : FA → FA → 𝓤 ̇
 []      ▶ t       = 𝟘
 (x ∷ s) ▶ []      = (x ∷ s) ◗ []
 (x ∷ s) ▶ (y ∷ t) = ((x ∷ s) ◗ (y ∷ t)) + (x ≡[X] y × (s ▶ t))

 ▶-lemma : (x y : X) (s : List X) → y ≡ x ⁻ → (x ∷ y ∷ s) ▶ s
 ▶-lemma x _ []      refl = to-≡[X] {x ⁻} refl , ⋆
 ▶-lemma x _ (z ∷ s) refl = inl (to-≡[X]  {x ⁻} refl ,
                                 to-≡[X]  {z}   refl ,
                                 to-≡[FA] {s}   refl)
\end{code}

The reduction relation _▷_ is defined in the module FreeGroup.lagda,
and its propositional, symmetric, reflexive, transitive closure gives
the relation _∾_ that we use in order to quotient the type FA to get
the group freely generated by A.

We now show that _▶_ defined above is logically equivalent to _▷_.

\begin{code}

 ▶-gives-▷ : {s t : FA} → s ▶ t → s ▷ t

 ▶-gives-▷ {[]} {t} r = 𝟘-elim r

 ▶-gives-▷ {x ∷ y ∷ s} {[]} (p , q) = [] , s , x ,
                                      ap (λ - → x ∷ - ∷ s) (from-≡[X] p) ,
                                      ((from-≡[FA] q)⁻¹)

 ▶-gives-▷ {x ∷ y ∷ s} {z ∷ t} (inl (p , q)) = γ (from-≡[X] p) (from-≡[FA] q)
  where
   γ : y ≡ x ⁻ → s ≡ z ∷ t → x ∷ y ∷ s ▷ z ∷ t
   γ p q = [] , s , x , ap (λ - → x ∷ (- ∷ s)) p , (q ⁻¹)

 ▶-gives-▷ {x ∷ s} {y ∷ t} (inr (p , r)) = γ (from-≡[X] p) IH
  where
   IH : s ▷ t
   IH = ▶-gives-▷ r

   γ : x ≡ y → s ▷ t → (x ∷ s) ▷ (y ∷ t)
   γ refl = ∷-▷ x

 ▷-gives-▶ : {s t : FA} → s ▷ t → s ▶ t

 ▷-gives-▶ (u , v , x , refl , refl) = f u v x
  where
   f : (u v : FA) (x : X) → (u ++ [ x ] ++ [ x ⁻ ] ++ v) ▶ (u ++ v)
   f []      []      x = to-≡[X] {x ⁻} refl , ⋆
   f []      (y ∷ v) x = inl (to-≡[X] {x ⁻} refl , to-≡[X] {y} refl , to-≡[FA] {v} refl)
   f (y ∷ u) v       x = inr (to-≡[X] {y} refl , f u v x)

\end{code}

The usual way to define the transitive closure of a relation (cf. the
file SRTclosure.lagda) applied to the relation _▶_ would increase
universe levels back to those of the relation _∾_.

In order to overcome this obstacle, we consider a type of redexes.

\begin{code}

 redex : FA → 𝓤 ̇
 redex []          = 𝟘
 redex (x ∷ [])    = 𝟘
 redex (x ∷ y ∷ s) = (y ≡[X] (x ⁻)) + redex (y ∷ s)

 reduct : (s : FA) → redex s → FA
 reduct (x ∷ y ∷ s) (inl p) = s
 reduct (x ∷ y ∷ s) (inr r) = x ∷ reduct (y ∷ s) r

\end{code}

The idea behind the above definitions is that we want that the
relation s ▶ t holds if and only the word t is the reduct of s at some
redex r, which is what we prove next:

\begin{code}

 lemma-reduct→ : (s : FA) (r : redex s) → s ▶ reduct s r
 lemma-reduct→ (x ∷ y ∷ s) (inl p) = ▶-lemma x y s (from-≡[X] p)
 lemma-reduct→ (x ∷ y ∷ s) (inr r) = inr (to-≡[X] {x} refl ,
                                         lemma-reduct→ (y ∷ s) r)

 lemma-reduct← : (s t : FA) → s ▶ t → Σ r ꞉ redex s , reduct s r ≡ t
 lemma-reduct← (x ∷ [])    (z ∷ t) (inl ())
 lemma-reduct← (x ∷ [])    (z ∷ t) (inr ())
 lemma-reduct← (x ∷ y ∷ s) []      (p , q)       = inl p , from-≡[FA] q
 lemma-reduct← (x ∷ y ∷ s) (z ∷ t) (inl (p , q)) = inl p , from-≡[FA] q
 lemma-reduct← (x ∷ y ∷ s) (z ∷ t) (inr (p , r)) = inr (pr₁ IH) ,
                                                   ap₂ _∷_ (from-≡[X] p) (pr₂ IH)
  where
   IH : Σ r ꞉ redex (y ∷ s) , reduct (y ∷ s) r ≡ t
   IH = lemma-reduct← (y ∷ s) t r

\end{code}

Next we define a type of chains of redexes of length n and a
corresponding notion of reduct for such chains:

\begin{code}

 redex-chain : ℕ → FA → 𝓤 ̇
 redex-chain 0        s = 𝟙
 redex-chain (succ n) s = Σ r ꞉ redex s , redex-chain n (reduct s r)

 chain-reduct : (s : FA) (n : ℕ) → redex-chain n s → FA
 chain-reduct s 0        ρ       = s
 chain-reduct s (succ n) (r , ρ) = chain-reduct (reduct s r) n ρ

 chain-lemma→ : (s : FA) (n : ℕ) (ρ : redex-chain n s) → s ▷[ n ] chain-reduct s n ρ
 chain-lemma→ s 0        ρ       = refl
 chain-lemma→ s (succ n) (r , ρ) = reduct s r ,
                                   ▶-gives-▷ (lemma-reduct→ s r) ,
                                   chain-lemma→ (reduct s r) n ρ

 chain-lemma← : (s t : FA) (n : ℕ)
              → s ▷[ n ] t
              → Σ ρ ꞉ redex-chain n s , chain-reduct s n ρ ≡ t
 chain-lemma← s t 0        r           = ⋆ , r
 chain-lemma← s t (succ n) (u , b , c) = γ IH l
  where
   IH : Σ ρ ꞉ redex-chain n u , chain-reduct u n ρ ≡ t
   IH = chain-lemma← u t n c

   l : Σ r ꞉ redex s , reduct s r ≡ u
   l = lemma-reduct← s u (▷-gives-▶ b)

   γ : type-of IH
     → type-of l
     → Σ ρ' ꞉ redex-chain (succ n) s , chain-reduct s (succ n) ρ' ≡ t
   γ (ρ , refl) (r , refl) = (r , ρ) , refl

\end{code}

And with this we obtain a relation _≏_ whose propositional truncation
will be logically equivalent to the equivalence relation _∾_ used to
quotient FA to get the group freely generated by A. The relation _∾_
itself is the propositional truncation of a suitable relation _∿_,
which we now use for that purpose.

\begin{code}

 _≏_ : FA → FA → 𝓤 ̇
 s ≏ t = Σ m ꞉ ℕ ,
         Σ n ꞉ ℕ ,
         Σ ρ ꞉ redex-chain m s ,
         Σ σ ꞉ redex-chain n t , chain-reduct s m ρ  ≡[FA] chain-reduct t n σ

 ≏-gives-∿ : (s t : FA) → s ≏ t → s ∿ t
 ≏-gives-∿ s t (m , n , ρ , σ , p) = γ
  where
   a : s ▷⋆ chain-reduct s m ρ
   a = m , chain-lemma→ s m ρ

   b : t ▷⋆ chain-reduct t n σ
   b = n , chain-lemma→ t n σ

   c : Σ u ꞉ FA , (s ▷⋆ u) × (t ▷⋆ u)
   c = chain-reduct t n σ  , transport (s ▷⋆_) (from-≡[FA] p) a , b

   γ : s ∿ t
   γ = to-∿ s t c

 ∿-gives-≏ : (s t : FA) → s ∿ t → s ≏ t
 ∿-gives-≏ s t e = γ a
  where
   a : Σ u ꞉ FA , (s ▷⋆ u) × (t ▷⋆ u)
   a = from-∿ Church-Rosser s t e

   γ : type-of a → s ≏ t
   γ (u , (m , ρ) , (n , σ)) = δ b c
    where
     b : Σ ρ ꞉ redex-chain m s , chain-reduct s m ρ ≡ u
     b = chain-lemma← s u m ρ

     c : Σ σ ꞉ redex-chain n t , chain-reduct t n σ ≡ u
     c = chain-lemma← t u n σ

     δ : type-of b → type-of c → s ≏ t
     δ (ρ , p) (σ , q) = m , n , ρ , σ , to-≡[FA] (p ∙ q ⁻¹)

 open free-group-construction-step₁ pt

 _∥≏∥_ : FA → FA → 𝓤 ̇
 s ∥≏∥ t = ∥ s ≏ t ∥

 ∾-is-logically-equivalent-to-∥≏∥ : (s t : FA) → s ∾ t ⇔ s ∥≏∥ t
 ∾-is-logically-equivalent-to-∥≏∥ s t = ∥∥-functor (∿-gives-≏ s t) ,
                                       ∥∥-functor (≏-gives-∿ s t)
\end{code}

And so we also get a type equivalence, because logically equivalent
propositions are equivalent types:

\begin{code}

 ∿-is-equivalent-to-∥≏∥ : (s t : FA) → (s ∾ t) ≃ (s ∥≏∥ t)
 ∿-is-equivalent-to-∥≏∥ s t = logically-equivalent-props-are-equivalent
                               ∥∥-is-prop
                               ∥∥-is-prop
                               (lr-implication (∾-is-logically-equivalent-to-∥≏∥ s t))
                               (rl-implication (∾-is-logically-equivalent-to-∥≏∥ s t))
\end{code}

Being logically equivalent to an equivalence relation, the relation
∥≏∥ is itself an equivalence relation (this is proved in the module
SRT.lagda).

\begin{code}

 open free-group-construction-step₂ fe pe

 -∥≏∥- : EqRel {𝓤⁺} {𝓤} FA
 -∥≏∥- = _∥≏∥_ , is-equiv-rel-transport _∾_ _∥≏∥_ (λ s t → ∥∥-is-prop)
                 ∾-is-logically-equivalent-to-∥≏∥ ∾-is-equiv-rel
\end{code}

By a general construction in the module UF.Quotient.lagda, we conclude
that FA/∾ ≃ FA/∥≏∥. What is crucial for our purposes is that FA/∥≏∥
lives in the lower universe 𝓤⁺, as opposed to the original quotient
FA/∾, which lives in the higher universe 𝓤⁺⁺.

\begin{code}

 FA/∥≏∥ : 𝓤⁺ ̇
 FA/∥≏∥ = FA / -∥≏∥-

 FA/∾-is-equivalent-to-FA/∥≏∥ : FA/∾ ≃ FA/∥≏∥
 FA/∾-is-equivalent-to-FA/∥≏∥ = quotients-equivalent FA -∾- -∥≏∥-
                                (λ {s} {t} → ∾-is-logically-equivalent-to-∥≏∥ s t)

 native-universe-of-free-group : universe-of ⟨ free-group A ⟩ ≡ 𝓤 ⁺⁺
 native-universe-of-free-group = refl

 resized-free-group-carrier : ⟨ free-group A ⟩ has-size 𝓤⁺
 resized-free-group-carrier = γ
  where
   γ : Σ F ꞉ 𝓤⁺ ̇ , F ≃ ⟨ free-group A ⟩
   γ = FA/∥≏∥ , ≃-sym FA/∾-is-equivalent-to-FA/∥≏∥

\end{code}

With this we get the proof of the first lemma needed for the main
theorem in this module. This relies on transporting group structures
along equivalences, which is implemented in the module Group.lagda
(unfortunately, one cannot apply univalence for that purpose, because
the types live in different universes and hence one can't form their
identity type, and so this transport has to be done manually).

\begin{code}

 small-free-group : Σ F ꞉ Group 𝓤⁺ , F ≅ free-group A
 small-free-group = resized-group (free-group A) resized-free-group-carrier

\end{code}

We say that a type has size 𝓥 if it is equivalent to some type in the
universe 𝓥, and that a map has size 𝓥 if its fibers all have size 𝓥.
See the module UF.Size.lagda. This notion of size for maps is
introduced and developed in the paper https://arxiv.org/abs/2102.08812
by Tom de Jong and Martin Escardo.

The native size of the universal map ηᴳʳᵖ : A → FA/∾ into the free
group is rather large - it jumps up two universe levels:

\begin{code}

 ηᴳʳᵖ-native-size : ηᴳʳᵖ is 𝓤⁺⁺ small-map
 ηᴳʳᵖ-native-size y = fiber ηᴳʳᵖ y , ≃-refl _

\end{code}

Using the above development, we can make it smaller.

In the following, the function η/∾ : FA → FA/∾ is the universal map
into the quotient (constructed in the module FreeGroup.lagda), and, by
definition, the universal map ηᴳʳᵖ : A → FA/∾ into the free group is
the composite η/∾ ∘ η where η : A → FA is the insertion of generators
before quotienting.

The following result is proved by quotient induction, which says that
in order to prove a property of all elements of the quotient, it
suffices to prove it for elements of the form η/∾ s with s : FA.

\begin{code}

 ηᴳʳᵖ-is-medium : ηᴳʳᵖ is 𝓤⁺ small-map
 ηᴳʳᵖ-is-medium = /-induction -∾- (λ y → fiber ηᴳʳᵖ y has-size 𝓤⁺)
                   (λ y → being-small-is-prop ua (fiber ηᴳʳᵖ y) 𝓤⁺) γ
  where
   e : (a : A) (s : FA) → (η/∾ (η a) ≡ η/∾ s) ≃ (η a ∥≏∥ s)
   e a s = (η/∾ (η a) ≡ η/∾ s) ≃⟨ I ⟩
           (η a ∾ s)           ≃⟨ II ⟩
           (η a ∥≏∥ s)         ■
    where
     I = logically-equivalent-props-are-equivalent
            (quotient-is-set -∾-)
            ∥∥-is-prop
            η/∾-relates-identified-points
            η/∾-identifies-related-points
     II = ∿-is-equivalent-to-∥≏∥ (η a) s

   d : (s : FA) → fiber ηᴳʳᵖ (η/∾ s) ≃ (Σ a ꞉ A , η a ∥≏∥ s)
   d s = (Σ a ꞉ A , η/∾ (η a) ≡ η/∾ s) ≃⟨ Σ-cong (λ a → e a s) ⟩
         (Σ a ꞉ A , η a ∥≏∥ s)          ■

   γ : (s : FA) → fiber ηᴳʳᵖ (η/∾ s) has-size 𝓤⁺
   γ s = (Σ a ꞉ A , η a ∥≏∥ s) , ≃-sym (d s)
    where
     notice : universe-of (fiber ηᴳʳᵖ (η/∾ s)) ≡ 𝓤⁺⁺
     notice = refl

\end{code}

But the above resizing of the map ηᴳʳᵖ is not small enough for our
purposes.

The fiber type Σ a ꞉ A , η a ≡ s lives in the universe 𝓤⁺. In the next
step we construct a copy of this fiber type in the first universe 𝓤₀.

The following construction also shows that the map η : A → FA has
decidable fibers, which is used implicitly in our definitions by
pattern matching.

\begin{code}

 native-universe-fiber-η : (s : FA) → universe-of (Σ a ꞉ A , η a ≡ s) ≡ 𝓤⁺
 native-universe-fiber-η s = refl

 fiber₀-η : FA → 𝓤₀ ̇
 fiber₀-η []             = 𝟘
 fiber₀-η (x ∷ y ∷ s)    = 𝟘
 fiber₀-η ((₀ , a) ∷ []) = 𝟙
 fiber₀-η ((₁ , a) ∷ []) = 𝟘

 NB-fiber₀-η-is-decidable : (s : FA) → fiber₀-η s + ¬ (fiber₀-η s)
 NB-fiber₀-η-is-decidable []             = inr id
 NB-fiber₀-η-is-decidable (x ∷ y ∷ s)    = inr id
 NB-fiber₀-η-is-decidable ((₀ , a) ∷ []) = inl ⋆
 NB-fiber₀-η-is-decidable ((₁ , a) ∷ []) = inr id

 fiber-η→ : (s : FA) → fiber₀-η s → (Σ a ꞉ A , η a ≡ s)
 fiber-η→ [] ()
 fiber-η→ (x ∷ y ∷ s) ()
 fiber-η→ (₀ , a ∷ []) ⋆ = a , refl
 fiber-η→ (₁ , a ∷ []) ()

 fiber-η← : (s : FA) → (Σ a ꞉ A , η a ≡ s) → fiber₀-η s
 fiber-η← .(η a) (a , refl) = ⋆

 η-fiber₀-η : (a : A) → fiber₀-η (η a)
 η-fiber₀-η a = ⋆

\end{code}

Using this, next we want to reduce the size of the type
Σ a ꞉ A , η a ∾ s, which we informally refer to
as "the ∾-fiber of s over η".

\begin{code}

 generator : FA → 𝓤 ̇
 generator s = Σ n ꞉ ℕ , Σ ρ ꞉ redex-chain n s , fiber₀-η (chain-reduct s n ρ)

 is-generator : FA → 𝓤 ̇
 is-generator s = ∥ generator s ∥

 the-∾-fibers-of-η-are-props : (s : FA) → is-prop (Σ a ꞉ A , η a ∾ s)
 the-∾-fibers-of-η-are-props s (a , e) (a' , e') = γ
  where
   α : η a ∾ η a'
   α = psrt-transitive (η a) s (η a') e (psrt-symmetric (η a') s e')

   β : a ≡ a'
   β = η-identifies-∾-related-points A-is-set α

   γ : (a , e) ≡ (a' , e')
   γ = to-subtype-≡ (λ x → ∥∥-is-prop) β

 ∾-fiber-η-lemma→ : (s : FA) → (Σ a ꞉ A , η a ∾ s) → is-generator s
 ∾-fiber-η-lemma→ s (a , e) = ∥∥-functor γ e
  where
   γ : η a ∿ s → Σ n ꞉ ℕ , Σ ρ ꞉ redex-chain n s , fiber₀-η (chain-reduct s n ρ)
   γ e = δ (d c)
    where
     c : Σ u ꞉ FA , (η a ▷⋆ u) × (s ▷⋆ u)
     c = from-∿ Church-Rosser (η a) s e

     d : type-of c → Σ n ꞉ ℕ , Σ ρ ꞉ redex-chain n s , chain-reduct s n ρ ≡ η a
     d (u , r , r₁) = δ r₂
      where
       p : η a ≡ u
       p = η-irreducible⋆ r

       r₂ : s  ▷⋆ η a
       r₂ = transport (s ▷⋆_) (p ⁻¹) r₁

       δ : s  ▷⋆ η a → Σ n ꞉ ℕ , Σ ρ ꞉ redex-chain n s , chain-reduct s n ρ ≡ η a
       δ (n , r₃) = (n , chain-lemma← s (η a) n r₃)

     δ : type-of (d c) → codomain γ
     δ (n , ρ , p) = n , ρ , transport fiber₀-η (p ⁻¹) (η-fiber₀-η a)

 ∾-fiber-η-lemma← : (s : FA) → is-generator s → (Σ a ꞉ A , η a ∾ s)
 ∾-fiber-η-lemma← s = ∥∥-rec (the-∾-fibers-of-η-are-props s) γ
  where
   γ : generator s → (Σ a ꞉ A , η a ∾ s)
   γ (n , ρ , i) = δ σ
    where
     r : s ▷[ n ] chain-reduct s n ρ
     r = chain-lemma→ s n ρ

     e : chain-reduct s n ρ ∾ s
     e = ∣ to-∿ (chain-reduct s n ρ) s (chain-reduct s n ρ , (0 , refl) , (n , r)) ∣

     σ : Σ a ꞉ A , η a ≡ chain-reduct s n ρ
     σ = fiber-η→ (chain-reduct s n ρ) i

     δ : type-of σ → Σ a ꞉ A , η a ∾ s
     δ (a , p) = a , transport (_∾ s) (p ⁻¹) e

\end{code}

And this is the desired size reduction:

\begin{code}

 ∾-fiber-η-lemma : (s : FA) → (Σ a ꞉ A , η a ∾ s) ≃ is-generator s
 ∾-fiber-η-lemma s = logically-equivalent-props-are-equivalent
                      (the-∾-fibers-of-η-are-props s)
                      ∥∥-is-prop
                      (∾-fiber-η-lemma→ s)
                      (∾-fiber-η-lemma← s)
\end{code}

With this we can further reduce the size of the universal map ηᴳʳᵖ:

\begin{code}

 ηᴳʳᵖ-is-small : ηᴳʳᵖ is 𝓤 small-map
 ηᴳʳᵖ-is-small = /-induction -∾- (λ y → fiber ηᴳʳᵖ y has-size 𝓤)
                  (λ y → being-small-is-prop ua (fiber ηᴳʳᵖ y) 𝓤) γ
  where
   e : (a : A) (s : FA) → (η/∾ (η a) ≡ η/∾ s) ≃ (η a ∾ s)
   e a s = logically-equivalent-props-are-equivalent
             (quotient-is-set -∾-)
             ∥∥-is-prop
             η/∾-relates-identified-points
             η/∾-identifies-related-points

   d : (s : FA) → fiber ηᴳʳᵖ (η/∾ s) ≃ is-generator s
   d s = (Σ a ꞉ A , η/∾ (η a) ≡ η/∾ s) ≃⟨ Σ-cong (λ a → e a s) ⟩
         (Σ a ꞉ A , η a ∾ s)           ≃⟨ ∾-fiber-η-lemma s ⟩
         is-generator s                ■

   γ : (s : FA) → fiber ηᴳʳᵖ (η/∾ s) has-size 𝓤
   γ s = is-generator s , ≃-sym (d s)

\end{code}

A result by Tom de Jong and Martin Escardo (https://arxiv.org/abs/2102.08812),
recorded in the module UF.Size.lagda and recently submitted for
publication in a paper about size, says that if a map has size 𝓥, and
if also its codomain has size 𝓥, then so does its domain.

\begin{code}

 free-group-small-gives-generating-set-small : ⟨ free-group A ⟩ has-size 𝓤
                                             → A has-size 𝓤
 free-group-small-gives-generating-set-small h = size-contravariance ηᴳʳᵖ ηᴳʳᵖ-is-small h


\end{code}

It follows that if there is a large, locally small set, then there is
a large group:

\begin{code}

large-group-with-no-small-copy : (Σ A ꞉ 𝓤 ⁺ ̇  , is-set A
                                               × is-large A
                                               × is-locally-small A)

                               → Σ F ꞉ Group (𝓤 ⁺) , ((G : Group 𝓤) → ¬ (G ≅ F))

large-group-with-no-small-copy {𝓤} (A , A-is-set , A-is-large , A-ls) = δ
 where
  open resize-free-group A A-is-set Id⟦ A-ls ⟧ ⟦ A-ls ⟧-refl  ≡⟦ A-ls ⟧-gives-≡

  γ : (Σ F ꞉ Group (𝓤 ⁺) , F ≅ free-group A)
    → (Σ F ꞉ Group (𝓤 ⁺) , ((G : Group 𝓤) → ¬ (G ≅ F)))
  γ (F , f , f-is-equiv , f-is-hom) = F , β
   where
    β : (G : Group 𝓤) → G ≅ F → 𝟘
    β G (g , g-is-equiv , g-is-hom) = α
     where
      h : ⟨ free-group A ⟩ has-size 𝓤
      h = ⟨ G ⟩ , f ∘ g , ∘-is-equiv g-is-equiv f-is-equiv

      α : 𝟘
      α = A-is-large (free-group-small-gives-generating-set-small h)

  δ : codomain γ
  δ = γ small-free-group

\end{code}

In the module BuraliForti.lagda we instantiate A to the type of
ordinals, which is large and locally small, to construct a large group
with no small copy.
