\section{Cubical Type Theory}\label{sec:cubical}

The computational properties of type theory as a foundation is what makes a proof
assistant like Agda possible. However, we have seen that adding axioms to the
theory breaks these properties. That poses a problem when there are axioms we would
like to make use of -- in particular the univalence axiom and higher inductive types.

One way to imbue HoTT with computational meaning is Cubical type theory~\cite{cohen2016cubical}.
The basic idea is to take the ``spaces as types''-interpretation of identity types very literally, as
a function from the interval. With this interpretation, univalence and HITs do not need to
be added axiomatically -- they become provable theorems~\cite{coquand2018higher}.
This section introduces the basic concepts of cubical type theory, Cubical Agda and the
Cubical library.

The main ingredient of cubical type theory is the interval type. It represents
the closed interval $[0,1]$ in and we can think of it as a HIT with two points
and an equality between them. Denote the interval by $\I$ and its two
endpoints by $\texttt{0}$ and $\texttt{1}$. An element along the interval is
represented by a variable $i : \I$

In addition to its elements, the interval supports three operations. The binary
operations $\land$ and $\lor$ and the unary operation $\sim$. In the geometric
interpretation these represent (respectively) $max, min$ and $1 - \_$. These
operations form a de Morgan algebra~\cite{mortberg2020cubical} (and in fact
$\I$ may be described as the free de Morgan algebra on a discrete set of
variable names $\{i, j, k ...\}$~\cite{cohen2016cubical}).

We can now define a cubical identity type as functions out of the interval type.
Concretely, an identity type $x =_A y$ is the type of functions $p : \texttt{I}
\rightarrow A$ such that $p(\texttt{0}) \equiv x$ and $p(\texttt{1}) \equiv y$.
This corresponds precisely to the notion of a path with endpoints $x$ and $y$ in
homotopy theory.

Using lambda-abstraction to define the functions we obtain the inference rules
seen in \autoref{eq:path-rules}.

\begin{figure}[h]
\begin{equation*}
  \begin{array}[t]{c}
    \Gamma \vdash a : A \qquad \Gamma \vdash b : A\\
    \hline
    \Gamma \vdash a =_A b \; Type\\
  \end{array}
  \qquad
  \begin{array}[t]{c}
    \Gamma, i : \I \vdash x(i) : A\\
    \hline
    \Gamma \vdash \lambda i.x(i) : x(\texttt{0}) =_A x(\texttt{1})\\
  \end{array}
  \qquad
  \begin{array}[t]{c}
    \Gamma \vdash p : a =_A b\\
    \hline
    \Gamma, i : \I \vdash p~i : A
  \end{array}
\end{equation*}
  \caption{Introduction-, formation- and elimination-rules for cubical paths}
  \label{eq:path-rules}
\end{figure}

By iterating this construction we obtain higher homotopies. $\I \ra A$
represents paths in $A$, $\I \ra \I \ra A$ squares, $\I \ra \I \ra \I \ra A$ the
eponymous cubes and so on.

Composition of paths is slightly involved. The most natural notion of composition
is actually ternary because it corresponds to "putting a lid" on an open box. Given
paths $p : x = y$, $q : y = z$ and $r : z = w$ the ternary composition is the dotted line
in \autoref{fig:doublecomp}.
\begin{figure}[h]
\centering
\begin{tikzcd}
  x \arrow[r, dashed] \arrow[d, "p"'] & w \arrow[d, "r^{-1}"] \\
  y \arrow[r, "q"']                   & z
\end{tikzcd}
\label{fig:doublecomp}
\caption{Composition of $p,q,r$}
\end{figure}

Note that the right wall is inverted to be parallel with the left.
To obtain binary composition $p \cdot q$ we fill in the box where the right-hand
wall is $\refl_z$ (it does not actually matter which wall we choose).

\subsection{Cubical Agda}
Cubical Agda~\cite{vezzosi2021cubical} implements support for cubical type
theory in Agda based on the development by Cohen et al.~\cite{cohen2016cubical}.
Additionally it extends the theory to support records and co-inductive types, a
general schema of HITs and univalence through \texttt{Glue} types. In this
section we look at some examples of Cubical Agda to get familiar with its
syntax.

As of Agda version 2.6.0, cubical mode can be activated with:
\begin{code}
{-# OPTIONS --cubical #-}
\end{code}

First, let us consider the cubical path type as introduced in the preceding
section. The interval type is denoted by $\I$, its two end-points by $i0$ and
$i1$ and the operations by $\_\land\_, \_\lor\_, \sim\_$. The most basic notion
of a path is actually the heterogenous/dependent path type:
\begin{code}[hide]
module _ where
open import Cubical.Foundations.Prelude
  using(subst ; _∙_)
open import Cubical.Core.Everything
  hiding(lineToEquiv)
open import Cubical.Data.Int
open import Cubical.Data.Int.Properties
import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
variable
  A : Type
postulate
\end{code}
\begin{code}
  HPath : (A : I → Type) → A i0 → A i1 → Type
\end{code}
The non-dependent identity types as discussed in \autoref{sec/identitytypes}
corresponds to a \texttt{HPath} over a constant family:
\begin{code}
Id : {A : Type} → A → A → Type
Id {A} x y = HPath (λ _ → A) x y
\end{code}

As one might expect, \texttt{refl} is the constant path
\begin{code}
refl : {x : A} → x ≡ x
refl {x = x} = λ i → x
\end{code}
and symmetry is defined using $\sim\_$:
\begin{code}
sym : {x y : A} → x ≡ y → y ≡ x
sym p = λ i → p (~ i)
\end{code}

Higher inductive types are defined by their point and path constructors. As an
example, consider the circle $S^1$ as introduced in \autoref{sec:HITs}.

\begin{code}
data S¹ : Type where
  base : S¹
  loop : base ≡ base
\end{code}

Defining functions out of HITs is done by pattern matching. Notice the variable
\texttt{i:\I} which represents ``varying along the path''.
This is the function from the circle to itself which reverses the direction of the loop.

\begin{code}
reverse : S¹ → S¹
reverse base = base
reverse (loop i) = sym loop i
\end{code}

This is very much like $rec_{S^1}$. In order to define a function we require a point (\texttt{base})
and loop (\texttt{sym loop})at that point. Since paths in Cubical agda are functions from the interval,
the loop also includes an argument \texttt{i} which we supply to \texttt{sym loop}, representing
travelling along the path.

Similarly, let us define the helix and winding number from \autoref{sec:HITs}.
\begin{code}
helix : S¹ → Type
helix base = ℤ
helix (loop i) = ua succEquiv i
\end{code}
\begin{code}[hide]
  where
  open Cubical.Foundations.Univalence using (ua)
  succEquiv : ℤ ≃ ℤ
  succEquiv = (sucℤ , isoToIsEquiv (iso sucℤ predℤ sucPred predSuc))
\end{code}
\begin{code}
encode : (x : S¹) → base ≡ x → helix x
encode _ p = subst helix p (pos 0)

winding : base ≡ base → ℤ
winding = encode base
\end{code}

Since everything computes, we do not need to evoke any computation rules to show that
this function computes the winding number. Each case is witnessed directly by $\refl$.
\begin{code}
_ : winding loop ≡ 1
_ = refl

_ : winding (loop ∙ loop) ≡ 2
_ = refl

_ : winding (sym loop) ≡ (- 1)
_ = refl
\end{code}


%Explain this when its needed in the formalization
%Note that the endpoints of a path must align with the mapping of points, and
%this alignment must be \emph{judgemental}.
%
%As a (somewhat contrived) examples consider a type just like the circle, except
%its loop is indexed by a boolean.
%\begin{code}
%data IndexedS¹ : Type where
  %baseI : IndexedS¹
  %loopI : Bool → baseI ≡ baseI
%
%-- this will not work because "true != if x then true else true of type Bool"
  %-- constTrue' : IndexedS¹ → Bool
  %-- constTrue' baseI = true
  %-- constTrue' (loopI b i) = if b then true else true
%constTrue' : IndexedS¹ → Bool
%constTrue' baseI = true
%constTrue' (loopI false i) = true
%constTrue' (loopI true i) = true
%\end{code}


In addition to the cubical mode, Vezzosi, M\"ortberg and Cavallo develop and
maintain a cubical standard library~\footnote[1]{A standard library for Cubical
  Agda: \url{https://github.com/agda/cubical}} containing useful data types,
functions and proofs.

\subsection{Function Extensionality and Univalence}

In addition to the higher inductive types, a benefit of cubical type theories
is that they make it possible to prove
useful results that are usually only axiomatically defined. Two
prominent examples are function extensionality and Voevodsky's univalence
axiom~\cite{voevodsky2014}.

In cubical type theory (and in particular in Cubical Agda) these are not axioms
at all, but provable theorems. Function extensionality is especially
straightforward: given two functions $f,g : A \ra B$ and a
family of paths $p : \Pi_{(x:A)}~f(x)~=_B~g(x)$, the proof simply swaps the
order of operations.
\begin{code}
funExt : {A B : Type} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funExt p i x = (p x) i
\end{code}
It is also possible to prove function extensionality from
univalence~\cite{gambino2016, bauer2011coq}, but the above is much
more direct.

Univalence is also provable in the sense that a term of the type
\begin{code}[hide]
postulate
  univalence' :
\end{code}
\begin{code}
    {A B : Type} → (A ≡ B) ≃ (A ≃ B)
\end{code}
can be constructed.

Univalence in Cubical Agda is implemented through a new type former called
\texttt{Glue}. Conceptually, \texttt{Glue} provides a way to construct lids
of open boxes in the universe given a family of types and equivalences over \texttt{I}.
We may think of it as a generalization of composition which allows a family of equivalences,
rather than a family of paths~\cite{1labUnivalence}.

In order to define \texttt{ua} of some equivalence $e$ we let the left wall be
$e$, the bottom $\refl$ and the right the identity equivalence.
\begin{figure}[h]
\centering
\begin{tikzcd}
  A \arrow[r, "\ua(e)", dashed] \arrow[d, "\rotatebox{90}{\(\sim\)}", "e"'] & B \arrow[d, "id", "\rotatebox{90}{\(\sim\)}"'] \\
  B \arrow[r, "\refl"']                         & B
\end{tikzcd}
\end{figure}

The result is one way of the equivalence above. The other direction is called \texttt{lineToEquiv}.
\begin{code}
  ua          : {A B : Type} → A ≃ B → A ≡ B
  lineToEquiv : {A B : Type} → A ≡ B → A ≃ B
\end{code}

\subsection{Canonicity}
The benefit of all this is canonicity. Since \texttt{ua} and HITs are non-axiomatic,
terms constructed by their use reduce to a normalized value. This means our
formalization actually computes the result of applying patches.

However, that is not entirely true.
There are two exceptions to canonicity at the time of writing:
\begin{enumerate}
  \item \texttt{transp} (the primitive used to implement \texttt{transport}) over
  inductive families, and
  \item \texttt{hcomp} (the primitive used to implement path composition) over inductive families.
\end{enumerate}

Inductive families refer to inductive types that are also indexed by some indexing type.
For example, \texttt{Vec A} is an inductive family over \texttt{A} indexed by integers,
and as such expressions like \texttt{transport (λ i → Vec A (p i)) [~]} do not reduce~\cite{vezzosi2021cubical}.
Canonicity-preserving support for inductive families and its inclusion in Cubical Agda is
an ongoing project~\footnote{https://github.com/agda/agda/issues/3733}. We will return
to the issue in \autoref{ch/conclusion}, as it relates to the formalizations and results
in \autoref{ch/formalization}.
