\section{Another Type-Theoretic Approach}\label{sec:attempt}

In this section we explain a different approach to modeling VCSs in homotopy
type theory based on a specific class of HITs called coequalizers. The basic
idea is again to take advantage of the groupoid structure of types by modeling a
VCS as a HIT with point constructors for contexts and path constructors for
patches.

By giving the paths explicitly with endpoints, the result is essentially a
(type-theoretic) coequalizer: the type of repository contexts quotiented by
patches between them. Then, functions out of this type can be defined through a
characterization of its patch space given by Kraus and von Raumer~\cite{kraus2019path}.

The goal of this approach is to define patch theories that are -- in some sense
-- \emph{semantic}. Operations and laws on patches should be definable in terms
of both their endpoints and the \emph{kind} of patch. Constructing such theories in
terms of higher inductive types leads to coequalizers.

We present an unsuccessful attempt at implementing this approach in Cubical Agda
along the results of Kraus and von Raumer, followed by a discussion of the
problems encountered.

\subsection{Repository HIT}

Aiming to construct a HIT in which point constructors are repository contexts and
path constructor represent patches, we arrive at an inclusion of some base type
into the HIT and one or more named paths with endpoints specified in the base type.

The result is much like the coequalizers discussed by Kraus and von Raumer.

The data of a coequalizer is a type $A$ and a doubly indexed family of types $\sim : A
\rightarrow A \rightarrow Type$ called a ``proof relevant relation'' on $A$. We
write $a \sim b$ for the type $\Pi_{(a,b : A)} \sim a~b$ of two related terms in
$A$ (leaving out explicit introduction of $a$ and $b$).
Then the coequalizer $A \quot{\sim}$ is a higher inductive type with points $[a]$ for
$a : A$ and paths $glue~p : [a] \equiv [b]$ for $p : a \sim b$~\cite{kraus2019path}.

In formal terms this is the introduction rule:
\begin{equation}
  \label{eq:coequalizer-intro}
  \begin{array}[t]{l}
    \Gamma \vdash A \; Type\\
    \Gamma, a~b : A \vdash a \sim b \; Type\\
    \hline
    \Gamma \vdash A \quot{\sim} \; Type\\
  \end{array}
\end{equation}

And the two formation rules:
\begin{equation}
  \begin{centering}
  \label{eq:coequalizer-formation}
  \begin{array}[t]{l}
    \Gamma \vdash a : A\\
    \hline
    \Gamma \vdash [a] : A \quot{\sim}\\
  \end{array}
  \qquad
  \begin{array}[t]{l}
    \Gamma \vdash p : a \sim b\\
    \hline
    \Gamma \vdash glue~p : [a] \equiv [b]
  \end{array}
  \end{centering}
\end{equation}

As a concrete running example we will consider a very simple VCS in which a
repository consists of a single value that can be either \texttt{Nothing} or
\texttt{Just x} for some term x, and a patch that sets a \texttt{Nothing} to
\texttt{Just} some value.

\begin{code}[hide]
{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Foundations.GroupoidLaws
module attempt where
\end{code}
\begin{code}
module repo (A : Type₀) where
  data Maybe : Type₀ where
    Nothing : Maybe
    Just    : A → Maybe

  data Simple : Type₀ where
    [_] : Maybe → Simple
    sett    : ∀ a → [ Nothing ] ≡ [ Just a ]
\end{code}

\subsection{Merge}

Kraus and von Raumer's characterization of the path spaces of such coequalizers
take the form of an induction principle for their paths. Given a coequalizer
like before, a term $a_0 : A$, and a path-indexed family
\[P : \Pi_{(b : A)} ([a_0] \equiv [b] \ra Type)\]
the induction principle gives a way to construct a term of the type:
\[\Pi_{(b : A)} \Pi_{(q : [a0] \equiv [b])} P~b~q\]
a dependent function out of the (based) path type of $A \quot{\sim}$.

For non-HIT types the J-rule is the appropriate such principle, but this is not
the case once we allow higher constructors. While the J-rule
adequately covers the reflexive identities, it does not cover identities
constructed by $glue$. We might try to remedy this by also requiring a term of
$P~(glue~s)$ for any $s : a_0 \sim b$, but this is also not sufficient. In
particular, such a construction is not closed under symmetry and transitivity of
identities.
The solution is to instead require an equivalence $P~q \simeq P (q \cdot
(glue~s))$ for each $q : [a_0] \equiv [ b ]$ and $s : b \sim c$.

The complete induction rule is given by:
[in Agda? (specialized to our repo type)]
\begin{code}[hide]
  postulate
    ind :
      {ℓ : Level}
      {a0 : Maybe}
      (P : {x : Maybe} → [ a0 ] ≡ [ x ] → Type ℓ)
      → P refl
      → ({x : A} → (p : [ a0 ] ≡ [ Nothing ]) → P p ≃ P (p ∙ sett x))
      -------------------------------------------------------------------
      → {b : Maybe} → (q : [ a0 ] ≡ [ b ]) → P q
\end{code}
\begin{equation}
  \label{eq:coequalizer-induction}
  \begin{centering}
    \begin{array}[t]{l}
      \Gamma \vdash a_0 : A\\
      \Gamma, b : A \vdash P : [a_0] \equiv [b] \ra Type\\
      \Gamma \vdash r : P~refl_{[a_0]}\\
      \Gamma, b~c : A, q : [a_0] \equiv [b], s : b \sim c \vdash P~q \simeq P~(q \cdot (glue~s))\\
      \hline
      \Gamma \vdash ind~r~e : \Pi_{(b : A)} \Pi_{q : [a_0] \equiv [b]} P~q
    \end{array}
  \end{centering}
\end{equation}

We will attempt to use this induction rule to define a merge function for our
example VCS. For this purpose we introduce the types of spans and cospans
indexed by their endpoints:

\begin{code}
  Span : Maybe → Maybe → Type₀
  Span x y = Σ[ a ∈ Maybe ] ( [ a ] ≡ [ x ] ) × ([ a ] ≡ [ y ])

  CoSpan : Maybe → Maybe → Type₀
  CoSpan x y = Σ[ b ∈ Maybe ] ([ x ] ≡ [ b ]) × ([ y ] ≡ [ b ])
\end{code}

and, since merging is a binary operation, a binary induction rule

\begin{code}
  bin-path-ind : {ℓ : Level} → (a0 : Maybe) →
    (P  : {b c : Maybe} → [ a0 ] ≡ [ b ] → [ a0 ] ≡ [ c ] → Type ℓ) →
    (P refl refl) →
    ({x : A} → (p : [ a0 ] ≡ [ Nothing ]) → P refl p ≃ P refl (p ∙ sett x)) →
    ({x : A} (p : [ a0 ] ≡ [ Nothing ]) →
      ({c : Maybe} (q : [ a0 ] ≡ [ c ]) → P p q)
      ≃ ({c : Maybe} (q : [ a0 ] ≡ [ c ]) → P (p ∙ sett x) q)) →
    ---------------------------------------------------------------------
    {b : Maybe} → (p : [ a0 ] ≡ [ b ]) → {c : Maybe} → (q : [ a0 ] ≡ [ c ]) → P p q
  bin-path-ind a0 P r e e' = ind (λ p → ({c : Maybe} → (q : [ a0 ] ≡ [ c ]) → P p q))
                                 (ind (λ p → P refl p) r e) e'
\end{code}

Armed with binary path induction we can define the trivial merge which simply
maps every span to the cospan reversing both patches.

\begin{code}
  mergeId : {x y : Maybe} → Span x y → CoSpan x y
  mergeId {x = x} {y = y} (base , p , q) =
    bin-path-ind base
                (λ _ _ → CoSpan x y)
                (base , (sym p , sym q))
                (λ _ → idEquiv _)
                (λ _ → idEquiv _)
    p q
\end{code}

\subsection{Result/Discussion}
Attempting to write more useful merges proved both laborious and difficult. In
particular, the final term of \texttt{bin-path-ind} is an equivalence of
(dependent) function types that is difficult to reason about and construct.

One possible intuition, in the case of merge, is that it represents an equivalence between
"ways to merge an arbitrary $q$ with $p$" and "ways to merge an arbitrary $q$ with $p \cdot sett x$".
However, this has not proven fruitful and despite efforts to construct more fitting equivalences
the result has been the same "reverse everything"-merge.

As presented, this approach leaves a lot to be desired. Apart from the trivial
merge, it does not provide an intuitive or useful way to define merges even for
very simple examples, and it is not immediately clear that it
extends to more complicated theories with multiple kinds of patches and patch
laws.

[ANOTHER CONCLUSION? WEIRD NOTE TO END ON]
