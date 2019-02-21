wMartin Escardo, 19th Feb 2019.

Injective types in univalent mathematics
----------------------------------------

Remark about the contents and organization of this Agda file.

       This is supposed to match precisely an article to be submitted
       for publication.

       This is an article-style version of the blackboard-style
       version InjectiveTypes.lagda. The blackboard presents the ideas
       as they have been developed, rather than the way they should be
       presented in an article submitted for publication, but still in
       a fully verified way.

       Here we tell the story, referring to the blackboard file for
       the routine proofs (which can be followed as links in the html
       version of this file). We have included the non-routine proofs,
       and some routine proofs that we feel should be added for the
       sake of flow of the text. We repeat the definitions of the
       notions studied here (in a definitionally equal way).

       The blackboard file likely has more information than that
       reported here. In particular, it keeps track better of what
       univalent foundations assumptions are used in each construction
       (univalence, function extensionality, propositional
       extensionality, existence of propositional truncations). We do
       keep track of resizing here explicitly: it is not a global
       assumption.

Abstract/introduction. We study the injective types and the
algebraically injective types in univalent mathematics, both in the
absence and the presence of propositional resizing. Injectivity is
defined by the surjectivity of the restriction map along any
embedding. Algebraic injectivity is defined by a given section of the
restriction map along any embedding. For the sake of generality, we
work without assuming (or rejecting) the principle of excluded middle,
and hence without assuming the axiom of choice either. Moreover, the
principle of excluded middle holds if and only if all types are
algebraicly injective, if and only if all types are injective, and so
there is nothing interesting to say in its presence. In the presence
of resizing, the main results are easy to state and pleasing: (1)
Injectivity is equivalent to the propositional truncation of algebraic
injectivity (this can be seen as form of choice that just holds). (2)
The algebraically injective types are precisely the retracts of
exponential powers of type universes. (2') The algebraically injective
sets are precisely the retracts of powersets, (2'') The algebraically
injective n+1-types are precisely retracts of exponential powers of
the universes of n-types. (3) The algebraically injective types are
also precisely the underlying objects of algebras of the partial map
classifier monad. A corollary of the above is that any universe is
embedded as a retract of any larger universe in the presence of
propositional resizing. In the absence of propositional resizing, we
have similar results but they have subtler statements and proofs that
need to keep track of universe levels rather explicitly. Most
constructions developed here are in the absense of propositional
resizing. We apply them, with the aid of a notion of algebraic
flabbiness, to derive the results mentioned above.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Univalence
open import UF-PropTrunc

\end{code}

We assume univalence and propositional truncation globally in this
article:

\begin{code}

module InjectiveTypes-article
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import Plus-Properties
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Embeddings
open import UF-Retracts
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-EquivalenceExamples
open import UF-UniverseEmbedding
open import UF-PropIndexedPiSigma
open import UF-IdEmbedding

\end{code}

Hence we get function extensionality and propositional extensionality:

\begin{code}

fe : FunExt
fe = FunExt-from-Univalence ua

pe : PropExt
pe 𝓤 = propext-from-univalence (ua 𝓤)

import InjectiveTypes
module blackboard = InjectiveTypes fe

\end{code}

We study the notions of algebraically injective type (data), injective
type (property) and their relationships.

Algebraic injectivity stipulates a given section f ↦ f' of the
restriction map g ↦ g ∘ j:

\begin{code}

ainjective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
ainjective-type D 𝓤 𝓥 = {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
                      → (f : X → D) → Σ \(f' : Y → D) → f' ∘ j ∼ f

\end{code}

Injectivity stipulates that the restriction map is a surjection:

\begin{code}

injective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
injective-type D 𝓤 𝓥 = {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
                      → (f : X → D) → ∃ \(g : Y → D) → g ∘ j ∼ f
\end{code}

Universes are algebraicly injective, in at least two ways.

\begin{code}

_╲_ _╱_ :  {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → 𝓦 ̇) → (X → Y) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇)
(f ╲ j) y = Σ \(w : fiber j y) → f(pr₁ w)
(f ╱ j) y = Π \(w : fiber j y) → f(pr₁ w)


\end{code}

The crucial idea behind the following two statements is that a sum
indexed by a proposition (the fiber) is (equivalent, and hence) equal,
to any of its summands, and a product indexed by a proposition is
equal to any of its factors, and the fiber is a propositino when j is
an embedding.

\begin{code}

╲-is-extension : {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
               → (f : X → 𝓤 ⊔ 𝓥 ̇) → f ╲ j ∘ j ∼ f
╲-is-extension {𝓤} {𝓥} j i f x = eqtoid (ua (𝓤 ⊔ 𝓥)) ((f ╲ j ∘ j) x) (f x)
                                   (prop-indexed-sum (i (j x)) (x , refl))

╱-is-extension : {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
               → (f : X → 𝓤 ⊔ 𝓥 ̇) → f ╱ j ∘ j ∼ f
╱-is-extension {𝓤} {𝓥} j i f x = eqtoid (ua (𝓤 ⊔ 𝓥)) ((f ╱ j ∘ j) x) (f x)
                                   (prop-indexed-product (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥))
                                                         (i (j x)) (x , refl))

universes-are-ainjective-Σ : ainjective-type (𝓤 ⊔ 𝓥 ̇) 𝓤 𝓥
universes-are-ainjective-Σ {𝓤} {𝓥} j e f = (f ╲ j , ╲-is-extension j e f)

universes-are-ainjective-Π : ainjective-type (𝓤 ⊔ 𝓥 ̇) 𝓤 𝓥
universes-are-ainjective-Π {𝓤} {𝓥} j e f = (f ╱ j , ╱-is-extension j e f)

universes-are-ainjective-particular : ainjective-type (𝓤 ̇) 𝓤 𝓤
universes-are-ainjective-particular = universes-are-ainjective-Π

\end{code}

For y:Y not in the image of j, the extensions give 𝟘 and 𝟙 respectively:

\begin{code}

Σ-extension-out-of-range : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
                         → (y : Y) → ((x : X) → j x ≢ y)
                         → (f ╲ j) y ≃ 𝟘 {𝓣}
Σ-extension-out-of-range f j y φ = prop-indexed-sum-zero (uncurry φ)


Π-extension-out-of-range : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
                         → (y : Y) → ((x : X) → j x ≢ y)
                         → (f ╱ j) y ≃ 𝟙 {𝓣}
Π-extension-out-of-range {𝓤} {𝓥} {𝓦} f j y φ = prop-indexed-product-one (fe (𝓤 ⊔ 𝓥) 𝓦) (uncurry φ)

\end{code}

With excluded middle, this would give that the Σ and Π extensions have
the same sum and product as the non-extended maps, respectively, but
excluded middle is not needed:

\begin{code}

same-Σ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
       → Σ f ≃ Σ (f ╲ j)
same-Σ = blackboard.same-Σ

same-Π : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
       → Π f ≃ Π (f ╱ j)
same-Π = blackboard.same-Π

\end{code}

The proofs of the above are routine.

The two extensions are left and right Kan extensions in the following
sense, without the need to assume that j is an embedding. First, a
map X → 𝓤, when X is viewed as a ∞-groupoid and hence an ∞-category,
and when 𝓤 is viewed as the ∞-generalization of the category of sets,
can be considered as a sort of ∞-presheaf, because its functoriality
is automatic. Then we can consider natural transformations between
such ∞-presheafs. But again the naturality condition is automatic.  We
denote by _≾_ the type of natural transformations between such
∞-presheafs.

\begin{code}

_[_] : {X : 𝓤 ̇} (f : X → 𝓥 ̇) {x y : X} → Id x y → f x → f y
f [ refl ] = id

functoriality∙ : {X : 𝓤 ̇} (f : X → 𝓥 ̇) {x y z : X} (p : Id x y) (q : Id y z)
               → f [ p ∙ q ] ≡ f [ q ] ∘ f [ p ]
functoriality∙ f refl refl = refl

_≾_ : {X : 𝓤 ̇} → (X → 𝓥 ̇) → (X → 𝓦 ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
f ≾ g = (x : domain f) → f x → g x

naturality : {X : 𝓤 ̇} (f : X → 𝓥 ̇) (g : X → 𝓦 ̇) (τ : f ≾ g) {x y : X} (p : x ≡ y)
           → τ y ∘ f [ p ] ≡ g [ p ] ∘ τ x
naturality f g τ refl = refl

\end{code}

With this notation, we have:

\begin{code}

ηΣ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
   → f ≾ f ╲ j ∘ j
ηΣ f j x B = (x , refl) , B


ηΠ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y)
   → f ╱ j ∘ j ≾ f
ηΠ f j x A = A (x , refl)

\end{code}

These actually follow from the following more general facts, which say
that the extension operators are left and right adjoint to the
restriction map g ↦ g ∘ j.

\begin{code}

╲-extension-left-Kan : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y) (g : Y → 𝓣 ̇)
                     → (f ╲ j ≾ g) ≃ (f ≾ g ∘ j)
╲-extension-left-Kan f j g = blackboard.Σ-extension-left-Kan f j g

╱-extension-right-Kan : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y) (g : Y → 𝓣 ̇)
                      → (g ≾ f ╱ j) ≃ (g ∘ j ≾ f)
╱-extension-right-Kan f j g = blackboard.Π-extension-right-Kan f j g

\end{code}

The proofs of the above are routine.

We also have that if j is an embedding then so are the extension maps
f ↦ f ╲ j and f ↦ f ╱ j:

\begin{code}

╲-extension-is-embedding : (X Y : 𝓤 ̇) (j : X → Y) → is-embedding j → is-embedding (_╲ j)
╲-extension-is-embedding {𝓤} X Y j i = s-is-embedding
 where
  s : (X → 𝓤 ̇) → (Y → 𝓤 ̇)
  s f = f ╲ j

  r : (Y → 𝓤 ̇) → (X → 𝓤 ̇)
  r g = g ∘ j

  rs : ∀ f → r (s f) ≡ f
  rs f = dfunext (fe 𝓤 (𝓤 ⁺)) (╲-is-extension j i f)

  sr : ∀ g → s (r g) ≡ (g ∘ j) ╲ j
  sr g = refl

  κ : (g : Y → 𝓤 ̇) → s (r g) ≾ g
  κ g y ((x , p) , C) = transport g p C

  M : (𝓤 ⁺) ̇
  M = Σ \(g : Y → 𝓤 ̇) → (y : Y) → is-equiv (κ g y)

  φ : (X → 𝓤 ̇) → M
  φ f = s f , e
   where
    e : (y : Y) → is-equiv (κ (s f) y)
    e y = qinvs-are-equivs (κ (s f) y) (δ , ε , η)
     where
      δ : (Σ \(w : fiber j y) → f(pr₁ w))
        → Σ \(t : fiber j y) → Σ (\(w : fiber j (j (pr₁ t))) → f (pr₁ w))
      δ ((x , p) , C) = (x , p) , (x , refl) , C
      η : (σ : s f y) → κ (s f) y (δ σ) ≡ σ
      η ((x , refl) , C) = refl
      ε : (τ : Σ (λ w → r (s f) (pr₁ w))) → δ (κ (s f) y τ) ≡ τ
      ε ((x , refl) , (x' , p') , C) = t x x' (pa x' x p') p' C (appa x x' p')
       where
         t : (x x' : X) (u : x' ≡ x) (p : j x' ≡ j x) (C : f x') → (ap j u ≡ p) →
             ((x' , p)    , (x' , refl) , C)
          ≡ (((x  , refl) , (x' , p)    , C) ∶ Σ \w → r (s f) (pr₁ w))
         t x .x refl p C refl = refl
         q : ∀ x x' → qinv (ap j {x} {x'})
         q x x' = equivs-are-qinvs (ap j) (embedding-embedding' j i x x')
         pa : ∀ x x' → j x ≡ j x' → x ≡ x'
         pa x x' = pr₁ (q x x')
         appa : ∀ x x' p' → ap j (pa x' x p') ≡ p'
         appa x x' = pr₂ (pr₂ (q x' x))

  γ : M → (X → 𝓤 ̇)
  γ (g , e) = r g

  φγ : ∀ m → φ (γ m) ≡ m
  φγ (g , e) = to-Σ-≡
                (dfunext (fe 𝓤 (𝓤 ⁺)) (λ y → eqtoid (ua 𝓤) (s (r g) y) (g y) (κ g y , e y)) ,
                 Π-is-prop (fe 𝓤 𝓤) (λ y → being-equiv-is-a-prop'' (fe 𝓤 𝓤) (κ g y)) _ e)

  γφ : ∀ f → γ (φ f) ≡ f
  γφ = rs

  φ-is-equiv : is-equiv φ
  φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

  φ-is-embedding : is-embedding φ
  φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

  ψ : M → (Y → 𝓤 ̇)
  ψ = pr₁

  ψ-is-embedding : is-embedding ψ
  ψ-is-embedding = pr₁-embedding (λ g → Π-is-prop (fe 𝓤 𝓤) (λ y → being-equiv-is-a-prop'' (fe 𝓤 𝓤) (κ g y)))

  s-is-comp : s ≡ ψ ∘ φ
  s-is-comp = refl

  s-is-embedding : is-embedding s
  s-is-embedding = comp-embedding φ-is-embedding ψ-is-embedding


╱-extension-is-embedding : (X Y : 𝓤 ̇) (j : X → Y) → is-embedding j → is-embedding (_╱ j)
╱-extension-is-embedding {𝓤} X Y j i = s-is-embedding
 where
  s : (X → 𝓤 ̇) → (Y → 𝓤 ̇)
  s f = f ╱ j

  r : (Y → 𝓤 ̇) → (X → 𝓤 ̇)
  r g = g ∘ j

  rs : ∀ f → r (s f) ≡ f
  rs f = dfunext (fe 𝓤 (𝓤 ⁺)) (╱-is-extension j i f)

  sr : ∀ g → s (r g) ≡ (g ∘ j) ╱ j
  sr g = refl

  κ : (g : Y → 𝓤 ̇) → g ≾ s (r g)
  κ g y C (x , p) = back-transport g p C

  M : (𝓤 ⁺) ̇
  M = Σ \(g : Y → 𝓤 ̇) → (y : Y) → is-equiv (κ g y)

  φ : (X → 𝓤 ̇) → M
  φ f = s f , e
   where
    e : (y : Y) → is-equiv (κ (s f) y)
    e y = qinvs-are-equivs (κ (s f) y) (δ , ε , η)
     where
      δ : (((f ╱ j) ∘ j) ╱ j) y → (f ╱ j) y
      δ C (x , p) = C (x , p) (x , refl)
      η : (C : ((f ╱ j ∘ j) ╱ j) y) → κ (s f) y (δ C) ≡ C
      η C = dfunext (fe 𝓤 𝓤) g
       where
        g : (w : fiber j y) → κ (s f) y (δ C) w ≡ C w
        g (x , refl) = dfunext (fe 𝓤 𝓤) h
         where
          h : (t : fiber j (j x)) → C t (pr₁ t , refl) ≡ C (x , refl) t
          h (x' , p') = transport (λ - → C - (pr₁ - , refl) ≡ C (x , refl) -) q refl
           where
            q : (x , refl) ≡ (x' , p')
            q = i (j x) (x , refl) (x' , p')
      ε : (a : (f ╱ j) y) → δ (κ (s f) y a) ≡ a
      ε a = dfunext (fe 𝓤 𝓤) g
       where
        g : (w : fiber j y) → δ (κ (s f) y a) w ≡ a w
        g (x , refl) = refl

  γ : M → (X → 𝓤 ̇)
  γ (g , e) = r g

  φγ : ∀ m → φ (γ m) ≡ m
  φγ (g , e) = to-Σ-≡
                (dfunext (fe 𝓤 (𝓤 ⁺)) (λ y → eqtoid (ua 𝓤) (s (r g) y) (g y) (≃-sym (κ g y , e y))) ,
                 Π-is-prop (fe 𝓤 𝓤) (λ y → being-equiv-is-a-prop'' (fe 𝓤 𝓤) (κ g y)) _ e)

  γφ : ∀ f → γ (φ f) ≡ f
  γφ = rs

  φ-is-equiv : is-equiv φ
  φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

  φ-is-embedding : is-embedding φ
  φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

  ψ : M → (Y → 𝓤 ̇)
  ψ = pr₁

  ψ-is-embedding : is-embedding ψ
  ψ-is-embedding = pr₁-embedding (λ g → Π-is-prop (fe 𝓤 𝓤) (λ y → being-equiv-is-a-prop'' (fe 𝓤 𝓤) (κ g y)))

  s-is-comp : s ≡ ψ ∘ φ
  s-is-comp = refl

  s-is-embedding : is-embedding s
  s-is-embedding = comp-embedding φ-is-embedding ψ-is-embedding

\end{code}

We need the following two somewhat technical results in applications
of injectivity to work on compact ordinals (reported in this
repository but not in this article). Their proofs are routine.

\begin{code}

iterated-╱ : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} (f : X → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇) (j : X → Y) (k : Y → Z)
           → ((f ╱ j) ╱ k) ∼ (f ╱ (k ∘ j))
iterated-╱ {𝓤} {𝓥} {𝓦} f j k z = eqtoid (ua (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (((f ╱ j) ╱ k) z) ((f ╱ (k ∘ j)) z)
                                   (blackboard.iterated-extension j k z)


retract-extension : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (g : X → 𝓣 ̇) (j : X → Y)
                  → ((x : X) → retract (f x) of (g x))
                  → ((y : Y) → retract ((f ╱ j) y) of ((g ╱ j) y))
retract-extension = blackboard.retract-extension

\end{code}

This completes our discussion of extensions of maps into universes.

Algebraically injectives are closed under retracts:

\begin{code}

retract-of-ainjective : (D' : 𝓦' ̇) (D : 𝓦 ̇)
                      → ainjective-type D 𝓤 𝓥
                      → retract D' of D
                      → ainjective-type D' 𝓤 𝓥
retract-of-ainjective D' D i (r , (s , rs)) {X} {Y} j e f = φ a
 where
  a : Σ \(f' : Y → D) → f' ∘ j ∼ s ∘ f
  a = i j e (s ∘ f)
  φ : (Σ \(f' : Y → D) → f' ∘ j ∼ s ∘ f) → Σ \(f'' : Y → D') → f'' ∘ j ∼ f
  φ (f' , h) = r ∘ f' , (λ x → ap r (h x) ∙ rs (f x))

equiv-to-ainjective : (D' : 𝓦' ̇) (D : 𝓦 ̇)
                    → ainjective-type D 𝓤 𝓥
                    → D' ≃ D
                    → ainjective-type D' 𝓤 𝓥
equiv-to-ainjective D' D i e = retract-of-ainjective D' D i (equiv-retract-l e)

\end{code}

And under products:

\begin{code}

Π-ainjective : {A : 𝓣 ̇} {D : A → 𝓦 ̇}
             → ((a : A) → ainjective-type (D a) 𝓤 𝓥)
             → ainjective-type (Π D) 𝓤 𝓥
Π-ainjective {𝓣}  {𝓦} {𝓤} {𝓥} {A} {D} i {X} {Y} j e f = f' , g
 where
  l : (a : A) → Σ \(h : Y → D a) → h ∘ j ∼ (λ x → f x a)
  l a = (i a) j e (λ x → f x a)
  f' : Y → (a : A) → D a
  f' y a = pr₁ (l a) y
  g : f' ∘ j ∼ f
  g x = dfunext (fe 𝓣 𝓦) (λ a → pr₂ (l a) x)

\end{code}

And hence exponential powers:

\begin{code}

power-of-ainjective : {A : 𝓣 ̇} {D : 𝓦 ̇}
                    → ainjective-type D 𝓤 𝓥
                    → ainjective-type (A → D) 𝓤 𝓥
power-of-ainjective i = Π-ainjective (λ a → i)

\end{code}

An algebraically injective type is a retract of every type it is
embedded into:

\begin{code}

ainjective-retract-of-subtype : (D : 𝓦 ̇) → ainjective-type D 𝓦 𝓥
                              → (Y : 𝓥 ̇) → D ↪ Y → retract D of Y
ainjective-retract-of-subtype D i Y (j , e) = pr₁ a , j , pr₂ a
 where
  a : Σ \(f' : Y → D) → f' ∘ j ∼ id
  a = i j e id

\end{code}

The identity-type former Id is an embedding X → (X → 𝓤). The proof
requires some insight and can be found in another module.

\begin{code}

Id-is-embedding : {X : 𝓤 ̇} → is-embedding(Id {𝓤} {X})
Id-is-embedding {𝓤} = UA-Id-embedding (ua 𝓤) fe

\end{code}

From this we conclude that algebraically injective types are powers of
universes:

\begin{code}

ainjective-is-retract-of-power-of-universe : (D : 𝓤 ̇)
                                           → ainjective-type D 𝓤  (𝓤 ⁺)
                                           → retract D of (D → 𝓤 ̇)
ainjective-is-retract-of-power-of-universe {𝓤} D i = ainjective-retract-of-subtype D i (D → 𝓤 ̇)
                                                      (Id , Id-is-embedding)

\end{code}

The above results, when combined together in the obvious way, almost
give directly that the algebraically injective types are precisely the
retracts of exponential powers of universes, but there is a universe
mismatch.

Keeping track of the universes to avoid the mismatch, what we get
instead is a resizing theorem:

\begin{code}

ainjective-resizing₀ : (D : 𝓤 ̇) → ainjective-type D 𝓤 (𝓤 ⁺) → ainjective-type D 𝓤 𝓤
ainjective-resizing₀ {𝓤} D i = φ (ainjective-is-retract-of-power-of-universe D i)
 where
  φ : retract D of (D → 𝓤 ̇) → ainjective-type D 𝓤 𝓤
  φ = retract-of-ainjective D (D → 𝓤 ̇) (power-of-ainjective (universes-are-ainjective-Π))

\end{code}

A further resizing for-free construction is possible by considering a
notion of flabbiness as data (rather than as property, as in the
1-topos literature).

The notion of flabbiness used in topos theory is defined with
truncated Σ, that is, ∃. We refer to the notion defined with Σ as
algebraic flabiness.

\begin{code}

aflabby : 𝓦 ̇ → (𝓤 : Universe) → 𝓦 ⊔ 𝓤 ⁺ ̇
aflabby D 𝓤 = (P : 𝓤 ̇) → is-prop P → (f : P → D) → Σ \(d : D) → (p : P) → d ≡ f p

\end{code}

Algebraically flabby types are pointed:

\begin{code}

aflabby-pointed : (D : 𝓦 ̇) → aflabby D 𝓤 → D
aflabby-pointed D φ = pr₁ (φ 𝟘 𝟘-is-prop unique-from-𝟘)

\end{code}

And algebraically injective types (in the proof-relevant way we have
defined them) are aflabby, because maps P → 𝟙 from propositions P are
embeddings:

\begin{code}

ainjective-types-are-aflabby : (D : 𝓦 ̇) → ainjective-type D 𝓤 𝓥 → aflabby D 𝓤
ainjective-types-are-aflabby {𝓦} {𝓤} {𝓥} D i P h f = pr₁ (i (λ p → *) (prop-embedding P h 𝓥) f) * ,
                                                     pr₂ (i (λ p → *) (prop-embedding P h 𝓥) f)


\end{code}

The interesting thing is that the universe 𝓥 is forgotten in this
construction, with only 𝓤 remaining, particularly regarding this
converse, which says that algebraically flabby types are algebraically
injective:

\begin{code}

aflabby-types-are-ainjective : (D : 𝓦 ̇) → aflabby D (𝓤 ⊔ 𝓥) → ainjective-type D 𝓤 𝓥
aflabby-types-are-ainjective D φ {X} {Y} j e f = f' , p
 where
  f' : Y → D
  f' y = pr₁ (φ (fiber j y) (e y) (f ∘ pr₁))
  p : (x : X) → f' (j x) ≡ f x
  p x = q (x , refl)
   where
    q : (w : fiber j (j x)) → f' (j x) ≡ f (pr₁ w)
    q = pr₂ (φ (fiber j (j x)) (e (j x)) (f ∘ pr₁))

\end{code}

We then get this resizing theorem by composing the conversions between
algebraic flabiness and injectivity:

\begin{code}

ainjective-resizing₁ : (D : 𝓦 ̇) → ainjective-type D (𝓤 ⊔ 𝓣) 𝓥 → ainjective-type D 𝓤 𝓣
ainjective-resizing₁ D i j e f = aflabby-types-are-ainjective D (ainjective-types-are-aflabby D i) j e f

\end{code}

We record two particular cases that may make this clearer:

\begin{code}

ainjective-resizing₂ : (D : 𝓦 ̇) → ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤 𝓤
ainjective-resizing₂ = ainjective-resizing₁

ainjective-resizing₃ : (D : 𝓦 ̇) → ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤₀ 𝓤
ainjective-resizing₃ = ainjective-resizing₁

\end{code}

This is resizing down.

The type Ω 𝓤 of propositions of a universe 𝓤 is algebraically
flabby. More generally:

\begin{code}

Ω-aflabby : {𝓤 𝓥 : Universe} → aflabby (Ω (𝓤 ⊔ 𝓥)) 𝓤
Ω-aflabby {𝓤} {𝓥} P i f = (Q , j) , c
 where
  Q : 𝓤 ⊔ 𝓥 ̇
  Q = (p : P) → f p holds
  j : is-prop Q
  j = Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥)) (λ p → holds-is-prop (f p))
  c : (p : P) → Q , j ≡ f p
  c p = to-Σ-≡ (t , being-a-prop-is-a-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) _ _)
   where
      g : Q → f p holds
      g q = q p
      h : f p holds → Q
      h r p' = transport (λ - → f - holds) (i p p') r
      t : Q ≡ f p holds
      t = pe (𝓤 ⊔ 𝓥) j (holds-is-prop (f p)) g h

\end{code}

Therefore it is injective:

\begin{code}

Ω-ainjective : ainjective-type (Ω (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Ω-ainjective {𝓤} {𝓥} = aflabby-types-are-ainjective (Ω (𝓤 ⊔ 𝓥)) (Ω-aflabby {𝓤 ⊔ 𝓥} {𝓤})

\end{code}

Another way to see this is that it is a retract of the universe by
propositional truncation. (Exercise, not included.)

Algebraic flabiness can also be applied to show that all types are
injective iff excluded middle holds.

\begin{code}

open import UF-ExcludedMiddle

EM-gives-pointed-types-aflabby : (D : 𝓦 ̇) → EM 𝓤 → D → aflabby D 𝓤
EM-gives-pointed-types-aflabby {𝓦} {𝓤} D em d P i f = h (em P i)
 where
  h : P + ¬ P → Σ \(d : D) → (p : P) → d ≡ f p
  h (inl p) = f p , (λ q → ap f (i p q))
  h (inr n) = d , (λ p → 𝟘-elim (n p))

\end{code}

For the converse, we consider, given a proposition P, the type P + ¬ P + 𝟙,
which, if it is algebraically flabby, gives the decidability of P.

\begin{code}

aflabby-EM-lemma : (P : 𝓦 ̇) → is-prop P → aflabby ((P + ¬ P) + 𝟙) 𝓦 → P + ¬ P
aflabby-EM-lemma {𝓦} P i φ = γ
 where
  D = (P + ¬ P) + 𝟙 {𝓦}
  f : P + ¬ P → D
  f (inl p) = inl (inl p)
  f (inr n) = inl (inr n)
  d : D
  d = pr₁ (φ (P + ¬ P) (decidability-of-prop-is-prop (fe 𝓦 𝓤₀) i) f)
  κ : (z : P + ¬ P) → d ≡ f z
  κ = pr₂ (φ (P + ¬ P) (decidability-of-prop-is-prop (fe 𝓦 𝓤₀) i) f)
  a : (p : P) → d ≡ inl (inl p)
  a p = κ (inl p)
  b : (n : ¬ P) → d ≡ inl (inr n)
  b n = κ (inr n)
  δ : (d' : D) → d ≡ d' → P + ¬ P
  δ (inl (inl p)) r = inl p
  δ (inl (inr n)) r = inr n
  δ (inr *)       r = 𝟘-elim (m n)
   where
    n : ¬ P
    n p = 𝟘-elim (+disjoint ((a p)⁻¹ ∙ r))
    m : ¬¬ P
    m n = 𝟘-elim (+disjoint ((b n)⁻¹ ∙ r))
  γ : P + ¬ P
  γ = δ d refl

\end{code}

From this we conclude:

\begin{code}

pointed-types-aflabby-gives-EM : ((D : 𝓦 ̇) → D → aflabby D 𝓦) → EM 𝓦
pointed-types-aflabby-gives-EM {𝓦} α P i = aflabby-EM-lemma P i (α ((P + ¬ P) + 𝟙) (inr *))

EM-gives-pointed-types-ainjective : EM (𝓤 ⊔ 𝓥) → (D : 𝓦 ̇) → D → ainjective-type D 𝓤 𝓥
EM-gives-pointed-types-ainjective em D d = aflabby-types-are-ainjective D (EM-gives-pointed-types-aflabby D em d)

pointed-types-ainjective-gives-EM : ((D : 𝓦 ̇) → D → ainjective-type D 𝓦 𝓤) → EM 𝓦
pointed-types-ainjective-gives-EM α = pointed-types-aflabby-gives-EM
                                       (λ D d → ainjective-types-are-aflabby D (α D d))

\end{code}

Returning to size issues, we now apply algebraic flabiness to show
that propositional resizing gives unrestricted algebraic injective
resizing.

The propositional resizing principle, from 𝓤 to 𝓥, that we consider
here says that every proposition in the universe 𝓤 has an equivalent
copy in the universe 𝓥 (this is consistent because it is implied by
excluded middle, but, as far as we are aware, there is no known
computational interpretation of this axiom).

We begin with this lemma:

\begin{code}

open import UF-Resizing

aflabbiness-resizing : (D : 𝓦 ̇) (𝓤 𝓥 : Universe) → propositional-resizing 𝓤 𝓥
                     → aflabby D 𝓥 → aflabby D 𝓤
aflabbiness-resizing D 𝓤 𝓥 R φ P i f = d , h
 where
  Q : 𝓥 ̇
  Q = resize R P i
  j : is-prop Q
  j = resize-is-a-prop R P i
  α : P → Q
  α = to-resize R P i
  β : Q → P
  β = from-resize R P i
  d : D
  d = pr₁ (φ Q j (f ∘ β))
  k : (q : Q) → d ≡ f (β q)
  k = pr₂ (φ Q j (f ∘ β))
  h : (p : P) → d ≡ f p
  h p = d           ≡⟨ k (α p) ⟩
        f (β (α p)) ≡⟨ ap f (i (β (α p)) p) ⟩
        f p         ∎

\end{code}

And from this it follows that the algebraic injectivity of a type with
respect to two given universes 𝓤 and 𝓥 implies its algebraic
injectivity with respect to all universes 𝓤' and 𝓥': we convert
back-and-forth between ainjectivity and aflabbiness:

\begin{code}

ainjective-resizing : propositional-resizing (𝓤' ⊔ 𝓥') 𝓤
                    → (D : 𝓦 ̇) → ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤' 𝓥'
ainjective-resizing {𝓤'} {𝓥'} {𝓤} {𝓦} {𝓥} R D i j e f = aflabby-types-are-ainjective D
                                                            (aflabbiness-resizing D (𝓤' ⊔ 𝓥') 𝓤 R
                                                              (ainjective-types-are-aflabby D i)) j e f

\end{code}

As an application of this and of the algebraic injectivity of universes, we have
that any universe is a retract of any larger universe.

We remark that for types that are not sets, sections are not
automatically embeddings (Shulman 2015, https://arxiv.org/abs/1507.03634).

But we can choose the retraction so that the section is an embedding,
in this case.

\begin{code}

universe-retract : Propositional-resizing
                 → (𝓤 𝓥 : Universe)
                 → Σ \(ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇)) → is-embedding (section ρ)
universe-retract R 𝓤 𝓥 = ρ , (lift-is-embedding ua)
 where
  a : ainjective-type (𝓤 ̇) 𝓤 𝓤
  a = universes-are-ainjective-Π {𝓤} {𝓤}
  b : is-embedding (lift 𝓥)
    → ainjective-type (𝓤 ̇) (𝓤 ⁺) ((𝓤 ⊔ 𝓥 )⁺)
    → retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇)
  b e i = ainjective-retract-of-subtype (𝓤 ̇) i (𝓤 ⊔ 𝓥 ̇) (lift 𝓥 , e)
  ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇)
  ρ = b (lift-is-embedding ua) (ainjective-resizing R (𝓤 ̇) a)

\end{code}

Here are are using the fact that every injective type is a retract of
any type in which it is embedded, in conjunction with resizing, and
that there is an embedding of any universe into any larger universe,
assuming univalence.

It may be of interest to unfold the above proof to see a direct
argument avoiding flabiness and injectivity:

\begin{code}

universe-retract-unfolded : Propositional-resizing
                          → (𝓤 𝓥 : Universe)
                          → Σ \(ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇)) → is-embedding (section ρ)
universe-retract-unfolded R 𝓤 𝓥 = (r , lift 𝓥 , rs) , lift-is-embedding ua
 where
  s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  s = lift 𝓥
  e : is-embedding s
  e = lift-is-embedding ua
  F : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  F Y = resize R (fiber s Y) (e Y)
  f : (Y : 𝓤 ⊔ 𝓥 ̇) → F Y → fiber s Y
  f Y = from-resize R (fiber s Y) (e Y)
  r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  r Y = (p : F Y) → pr₁ (f Y p)
  rs : (X : 𝓤 ̇) → r (s X) ≡ X
  rs X = γ
   where
    g : (Y : 𝓤 ⊔ 𝓥 ̇) → fiber s Y → F Y
    g Y = to-resize R (fiber s Y) (e Y)
    u : F (s X)
    u = g (s X) (X , refl)
    v : fiber s (s X)
    v = f (s X) u
    i : (Y : 𝓤 ⊔ 𝓥 ̇) → is-prop (F Y)
    i Y = resize-is-a-prop R (fiber s Y) (e Y)
    X' : 𝓤 ̇
    X' = pr₁ v
    a : r (s X) ≃ X'
    a = prop-indexed-product (fe 𝓤 𝓤) (i (s X)) u
    b : s X' ≡ s X
    b = pr₂ v
    c : X' ≡ X
    c = embedding-lc s e b
    d : r (s X) ≃ X
    d = transport (λ - → r (s X) ≃ -) c a
    γ : r (s X) ≡ X
    γ = eqtoid (ua 𝓤) (r (s X)) X d

\end{code}

As mentioned above, we almost have that the algebraically injective
types are precisely the retracts of exponential powers of universes,
upto a universe mismatch. This mismatch is side-steped by
propositional resizing:

\begin{code}

ainjective-characterization : propositional-resizing (𝓤 ⁺) 𝓤
                           → (D : 𝓤 ̇) → ainjective-type D 𝓤 𝓤
                                       ⇔ Σ \(X : 𝓤 ̇) → retract D of (X → 𝓤 ̇)
ainjective-characterization {𝓤} R D = a , b
 where
  a : ainjective-type D 𝓤 𝓤 → Σ \(X : 𝓤 ̇) → retract D of (X → 𝓤 ̇)
  a i = D , d
   where
    c : ainjective-type D 𝓤 (𝓤 ⁺)
    c = ainjective-resizing R D i
    d : retract D of (D → 𝓤 ̇)
    d = ainjective-is-retract-of-power-of-universe D c

  b : (Σ \(X : 𝓤 ̇) → retract D of (X → 𝓤 ̇)) → ainjective-type D 𝓤 𝓤
  b (X , r) = d
   where
    c : ainjective-type (X → 𝓤 ̇) 𝓤 𝓤
    c = power-of-ainjective universes-are-ainjective-Π
    d : ainjective-type D 𝓤 𝓤
    d = retract-of-ainjective D (X → 𝓤 ̇) c r

\end{code}

We now discuss injectivity, as defined above, in relation to algebraic
injectivity.

\begin{code}

injectivity-is-a-prop : (D : 𝓦 ̇) (𝓤 𝓥 : Universe)
                      → is-prop (injective-type D 𝓤 𝓥)
injectivity-is-a-prop = blackboard.injective.injectivity-is-a-prop pt

\end{code}

This is routine, using that propositions are closed under Π.

\begin{code}

ainjective-gives-injective : (D : 𝓦 ̇) → ainjective-type D 𝓤 𝓥 → injective-type D 𝓤 𝓥
ainjective-gives-injective D i j e f = ∣ i j e f ∣

∥ainjective∥-gives-injective : (D : 𝓦 ̇) → ∥ ainjective-type D 𝓤 𝓥  ∥ → injective-type D 𝓤 𝓥
∥ainjective∥-gives-injective {𝓦} {𝓤} {𝓥} D = ∥∥-rec (injectivity-is-a-prop D 𝓤 𝓥)
                                                    (ainjective-gives-injective D)

\end{code}

In order to relate injectivity to the propositional truncation of
algebraic injectivity, we first prove some facts we already proved for
algebraic injectivity for injectivity. These facts cannot be obtained
by reduction (in particular products of injectives are not necessarily
injectives, in the absence of choice, but exponential powers are).

\begin{code}

embedding-∥retract∥ : (D : 𝓦 ̇) (Y : 𝓥 ̇) (j : D → Y) → is-embedding j → injective-type D 𝓦 𝓥
                   → ∥ retract D of Y ∥
embedding-∥retract∥ D Y j e i = ∥∥-functor φ a
  where
   a : ∃ \r  → r ∘ j ∼ id
   a = i j e id
   φ : (Σ \r  → r ∘ j ∼ id) → Σ \r  → Σ \s → r ∘ s ∼ id
   φ (r , p) = r , j , p

retract-of-injective : (D' : 𝓤 ̇) (D : 𝓥 ̇)
                     → injective-type D 𝓦 𝓣
                     → retract D' of D
                     → injective-type D' 𝓦 𝓣
retract-of-injective D' D i (r , (s , rs)) {X} {Y} j e f = γ
  where
   i' : ∃ \(f' : Y → D) → f' ∘ j ∼ s ∘ f
   i' = i j e (s ∘ f)
   φ : (Σ \(f' : Y → D) → f' ∘ j ∼ s ∘ f) → Σ \(f'' : Y → D') → f'' ∘ j ∼ f
   φ (f' , h) = r ∘ f' , (λ x → ap r (h x) ∙ rs (f x))
   γ : ∃ \(f'' : Y → D') → f'' ∘ j ∼ f
   γ = ∥∥-functor φ i'

power-of-injective : {A : 𝓣 ̇} {D : 𝓣 ⊔ 𝓦 ̇}
                   → injective-type D       (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)
                   → injective-type (A → D) (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)
power-of-injective {𝓣} {𝓦} {𝓤} {𝓥} {A} {D} i {X} {Y} j e f = γ
  where
   g : X × A → D
   g = uncurry f
   k : X × A → Y × A
   k (x , a) = j x , a
   c : is-embedding k
   c = pair-fun-embedding j (λ x a → a) e (λ x → id-is-embedding)
   ψ : ∃ \(g' : Y × A → D) → g' ∘ k ∼ g
   ψ = i k c g
   φ : (Σ \(g' : Y × A → D) → g' ∘ k ∼ g) → (Σ \(f' : Y → (A → D)) → f' ∘ j ∼ f)
   φ (g' , h) = curry g' , (λ x → dfunext (fe 𝓣 (𝓣 ⊔ 𝓦)) (λ a → h (x , a)))
   γ : ∃ \(f' : Y → (A → D)) → f' ∘ j ∼ f
   γ = ∥∥-functor φ ψ

injective-∥retract∥-of-power-of-universe : (D : 𝓤 ̇)
                                        → injective-type D 𝓤 (𝓤 ⁺)
                                        → ∥ retract D of (D → 𝓤 ̇) ∥
injective-∥retract∥-of-power-of-universe {𝓤} D = embedding-∥retract∥ D (D → 𝓤 ̇) Id Id-is-embedding

\end{code}

With this we get a partial converse to the fact that truncated
algebraic injectivity implies injectivity:

\begin{code}

injective-gives-∥ainjective∥ : (D : 𝓤 ̇)
                           → injective-type D 𝓤 (𝓤 ⁺)
                           → ∥ ainjective-type D 𝓤 𝓤 ∥
injective-gives-∥ainjective∥ {𝓤} D i = γ
  where
   φ : retract D of (D → 𝓤 ̇) → ainjective-type D 𝓤 𝓤
   φ = retract-of-ainjective D (D → 𝓤 ̇) (power-of-ainjective universes-are-ainjective-Π)
   γ : ∥ ainjective-type D 𝓤 𝓤 ∥
   γ = ∥∥-functor φ (injective-∥retract∥-of-power-of-universe D i)


\end{code}

So, in summary, regarding the relationship between injectivity and
truncated injectivity, so far we know that

  ∥ ainjective-type D 𝓤 𝓥  ∥ → injective-type D 𝓤 𝓥

and

  injective-type D 𝓤 (𝓤 ⁺) → ∥ ainjective-type D 𝓤 𝓤 ∥,

and hence, using propositional resizing, we get the following
characterization of a particular case of injectivity in terms of
algebraic injectivity.

\begin{code}

injectivity-in-terms-of-ainjectivity' : propositional-resizing (𝓤 ⁺) 𝓤
                                      → (D : 𝓤  ̇) → injective-type D 𝓤 (𝓤 ⁺)
                                                   ⇔ ∥ ainjective-type D 𝓤 (𝓤 ⁺) ∥
injectivity-in-terms-of-ainjectivity' {𝓤} R D = a , b
  where
   a : injective-type D 𝓤 (𝓤 ⁺) → ∥ ainjective-type D 𝓤 (𝓤 ⁺) ∥
   a = ∥∥-functor (ainjective-resizing R D) ∘ injective-gives-∥ainjective∥ D
   b : ∥ ainjective-type D 𝓤 (𝓤 ⁺) ∥ → injective-type D 𝓤 (𝓤 ⁺)
   b = ∥ainjective∥-gives-injective D

\end{code}

We would like to do better than this. For that purpose, we consider
the lifting monad in conjunction with resizing.

\begin{code}

import Lifting
import LiftingAlgebras
import LiftingEmbeddingViaSIP

𝓛 : {𝓣 𝓤 : Universe} → 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛 {𝓣} {𝓤} X = Σ \(P : 𝓣 ̇) → (P → X) × is-prop P

𝓛-unit : {𝓣 𝓤 : Universe} (X : 𝓤 ̇) → X → 𝓛 {𝓣} X
𝓛-unit X x = 𝟙 , (λ _ → x) , 𝟙-is-prop

𝓛-unit-is-embedding : (X : 𝓤 ̇) → is-embedding (𝓛-unit {𝓣} X)
𝓛-unit-is-embedding {𝓤} {𝓣} X = LiftingEmbeddingViaSIP.η-is-embedding' 𝓣 𝓤 X (ua 𝓣) (fe 𝓣 𝓤)

joinop : {𝓣 𝓤 : Universe} → 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
joinop {𝓣} {𝓤} X = {P : 𝓣 ̇} → is-prop P → (P → X) → X

𝓛-alg-Law₀ : {𝓣 𝓤 : Universe} {X : 𝓤 ̇} → joinop {𝓣} X → 𝓤 ̇
𝓛-alg-Law₀ {𝓣} {𝓤} {X} ∐ = (x : X) → ∐ 𝟙-is-prop (λ (p : 𝟙) → x) ≡ x

𝓛-alg-Law₁ : {𝓣 𝓤 : Universe} {X : 𝓤 ̇} → joinop {𝓣} X → (𝓣 ⁺) ⊔ 𝓤 ̇
𝓛-alg-Law₁ {𝓣} {𝓤} {X} ∐ = (P : 𝓣 ̇) (Q : P → 𝓣 ̇) (i : is-prop P) (j : (p : P) → is-prop (Q p)) (f : Σ Q → X)
                                → ∐ (Σ-is-prop i j) f ≡ ∐ i (λ p → ∐ (j p) (λ q → f (p , q)))

𝓛-alg : {𝓣 𝓤 : Universe} → 𝓤 ̇ → (𝓣 ⁺) ⊔ 𝓤 ̇
𝓛-alg {𝓣} {𝓤} X = Σ \(∐ : joinop {𝓣} X) → 𝓛-alg-Law₀ ∐ × 𝓛-alg-Law₁ ∐

𝓛-alg-aflabby : {𝓣 𝓤 : Universe} {A : 𝓤 ̇} → 𝓛-alg {𝓣} A → aflabby A 𝓣
𝓛-alg-aflabby {𝓣} {𝓤} (∐ , κ , ι) P i f = ∐ i f , γ
 where
  γ : (p : P) → ∐ i f ≡ f p
  γ p = LiftingAlgebras.𝓛-alg-Law₀-gives₀' 𝓣 (pe 𝓣) (fe 𝓣 𝓣) (fe 𝓣 𝓤) ∐ κ P i f p

𝓛-alg-ainjective : (A : 𝓤 ̇) → 𝓛-alg {𝓣} A → ainjective-type A 𝓣 𝓣
𝓛-alg-ainjective A α = aflabby-types-are-ainjective A (𝓛-alg-aflabby α)

free-𝓛-algebra-ainjective : (X : 𝓣 ̇) → ainjective-type (𝓛 {𝓣} X) 𝓣 𝓣
free-𝓛-algebra-ainjective {𝓣} X = 𝓛-alg-ainjective (𝓛 X)
                                    (LiftingAlgebras.𝓛-algebra-gives-alg 𝓣
                                      (LiftingAlgebras.free-𝓛-algebra 𝓣 (ua 𝓣) X))
\end{code}

Because the unit of the lifting monad is an embedding, it follows that
algebraically injective types are retracts of underlying objects of
free algebras:

\begin{code}

ainjective-is-retract-of-free-𝓛-algebra : (D : 𝓣 ̇) → ainjective-type D 𝓣 (𝓣 ⁺) → retract D of (𝓛 {𝓣} D)
ainjective-is-retract-of-free-𝓛-algebra D i = ainjective-retract-of-subtype D i (𝓛 D)
                                                (𝓛-unit D , 𝓛-unit-is-embedding D)
\end{code}

With propositional resizing, the algebraically injective types are
precisely the retracts of the underlying objects of free algebras of
the lifting monad:

\begin{code}

ainjectives-in-terms-of-free-𝓛-algebras : (D : 𝓣 ̇) → propositional-resizing (𝓣 ⁺) 𝓣
                                        → ainjective-type D 𝓣 𝓣
                                        ⇔ Σ \(X : 𝓣 ̇) → retract D of (𝓛 {𝓣} X)
ainjectives-in-terms-of-free-𝓛-algebras {𝓣} D R =  a , b
  where
   a : ainjective-type D 𝓣 𝓣 → Σ \(X : 𝓣 ̇) → retract D of (𝓛 X)
   a i = D , ainjective-is-retract-of-free-𝓛-algebra D (ainjective-resizing R D i)
   b : (Σ \(X : 𝓣 ̇) → retract D of (𝓛 X)) → ainjective-type D 𝓣 𝓣
   b (X , r) = retract-of-ainjective D (𝓛 X) (free-𝓛-algebra-ainjective X) r

\end{code}

Now, instead of propositional resizing, we consider the
impredicativity of the universe 𝓤, which says that the type of
propositions in 𝓤, which lives in the next universe 𝓤 ⁺, has an
equivalent copy in 𝓤 (for the relationship between resizing and
impredicativity, see the module UF-Resizing).

\begin{code}

injectivity-in-terms-of-ainjectivity : Ω-impredicative 𝓤
                                     → (D  : 𝓤 ̇) → injective-type D 𝓤 𝓤
                                                 ⇔ ∥ ainjective-type D 𝓤 𝓤 ∥
injectivity-in-terms-of-ainjectivity {𝓤} ω₀ D = γ , ∥ainjective∥-gives-injective D
 where
  open import LiftingSize 𝓤
  L : 𝓤 ̇
  L = pr₁ (𝓛-impredicative-resizing ω₀ D)

  e : 𝓛 D ≃ L
  e = ≃-sym(pr₂ (𝓛-impredicative-resizing ω₀ D))

  down : 𝓛 D → L
  down = eqtofun e

  down-is-embedding : is-embedding down
  down-is-embedding = equivs-are-embeddings down (eqtofun-is-an-equiv e)

  ε : D → L
  ε = down ∘ 𝓛-unit D

  ε-is-embedding : is-embedding ε
  ε-is-embedding = comp-embedding (𝓛-unit-is-embedding D) down-is-embedding

  injective-retract-of-L : injective-type D 𝓤 𝓤 → ∥ retract D of L ∥
  injective-retract-of-L = embedding-∥retract∥ D L ε ε-is-embedding

  L-injective : ainjective-type L 𝓤 𝓤
  L-injective = equiv-to-ainjective L (𝓛 D) (free-𝓛-algebra-ainjective D) (≃-sym e)

  γ : injective-type D 𝓤 𝓤 → ∥ ainjective-type D 𝓤 𝓤 ∥
  γ j = ∥∥-functor φ (injective-retract-of-L j)
   where
    φ : retract D of L → ainjective-type D 𝓤 𝓤
    φ = retract-of-ainjective D L L-injective

\end{code}

Here are some corollaries:

\begin{code}

injective-resizing : Ω-impredicative 𝓤 → (𝓥 𝓦 : Universe) → propositional-resizing (𝓥 ⊔ 𝓦) 𝓤
                   → (D : 𝓤 ̇)
                   → injective-type D 𝓤 𝓤 → injective-type D 𝓥 𝓦
injective-resizing {𝓤} ω₀ 𝓥 𝓦 R D i = c
  where
   a : ∥ ainjective-type D 𝓤 𝓤 ∥
   a = pr₁ (injectivity-in-terms-of-ainjectivity ω₀ D) i
   b : ∥ ainjective-type D 𝓥 𝓦 ∥
   b = ∥∥-functor (ainjective-resizing R D) a
   c : injective-type D 𝓥 𝓦
   c = ∥ainjective∥-gives-injective D b

EM-gives-pointed-types-injective : EM 𝓤 → (D : 𝓤 ̇) → D → injective-type D 𝓤 𝓤
EM-gives-pointed-types-injective {𝓤} em D d = ainjective-gives-injective D
                                                 (EM-gives-pointed-types-ainjective em D d)

pointed-types-injective-gives-EM : Ω-impredicative 𝓤
                                  → ((D : 𝓤 ̇) → D → injective-type D 𝓤 𝓤) → EM 𝓤
pointed-types-injective-gives-EM {𝓤} i = blackboard.injective.pointed-types-injective-gives-EM
                                            pt i (ua 𝓤)

\end{code}

TODO. Code the results about injective sets and injective n+1-types
stated in the abstract.

TODO. To make sure, go over every single line of the 1586 lines of the
InjectiveTypes file to check we haven't forgotten to include anything
relevant.

Fixities:

\begin{code}

infix  7 _╲_
infix  7 _╱_
infixr 4 _≾_

\end{code}