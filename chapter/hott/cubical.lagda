\section{Cubical Type Theory}

One way to imbue HoTT with computational meaning [INTRODUCE THIS PROBLEM
SOMEWHERE] is Cubical type theory~\cite{cohen2016cubical}. The basic idea is to
take the ``types as spaces''-interpretation of identity types very literally, as
a function from an interval. In particular, it allows for non-axiomatic
implementations of univalence and higher inductive types~\cite{coquand2018higher}. This section
introduces the basic concepts of cubical type theory, Cubical Agda and the
Cubical library.

\subsection{The Interval Type}\label{sec:interval-type}
\begin{enumerate}
  \item the interval type as a HIT
  \item operations on the interval type (free de morgan algebra)
  \item paths
  \item the eponymous cubes
\end{enumerate}

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

\begin{figure}
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
open import Cubical.Core.Everything
variable
  A : Type
postulate
\end{code}
\begin{code}
  HPath : (A : I → Type) → A i0 → A i1 → Type
\end{code}
The non-dependent identity types as discussed in \autoref{sec:interval-type}
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
and symmetry (denoted by $\_^{-1}$) is defined using $\sim\_$:
\begin{code}
_⁻¹ : {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = λ i → p (~ i)
\end{code}

Higher inductive types are defined by their point and path constructors. As an
example, consider the circle $S^1$ as introduced in \autoref{sec:HITs}.

\begin{code}
data S¹ : Type where
  base : S¹
  loop : base ≡ base
\end{code}

Defining functions out of HITs is done by pattern matching. Notice the variable
$i:\I$ which represents ``varying along the path''.

\begin{code}
backwards : S¹ → S¹
backwards base = base
backwards (loop i) = loop (~ i)
\end{code}

[FUNCTION EXAMPLE GOES HERE]

Note that the endpoints of a path must align with the mapping of points, and
this alignment must be \emph{definitional}. [EXPLICIT EXAMPLE]

In addition to the cubical mode, Vezzosi, M\"ortberg and Cavallo develop and
maintain a cubical standard library~\footnote[1]{A standard library for Cubical
  Agda: \url{https://github.com/agda/cubical}} containing useful data types,
functions and proofs.

\subsection{Why Cubical Type Theory?}
\begin{enumerate}
  \item function extensionality
  \item univalence (Glue types?)
  \item HITs
  \item all of the above with canonicity (with two very annoying exceptions)
\end{enumerate}

The main benefit of cubical type theories is that they make it possible to prove
several useful results that are usually only axiomatically defined. Two
prominent examples are function extensionality and Voevodsky's univalence
axiom~\cite{voevodsky2014}.

In cubical type theory (and in particular in Cubical Agda) these are not axioms
at all, but provable theorems. Function extensionality is especially
straightforward: given two (possibly dependent) functions $f,g : A \ra B$ and a
family of paths $p : \Pi_{(x:A)}~f(x)~=_B~g(x)$, the proof simply swaps the
arguments to $p$:
\[funExt~p~i~x = p~x~i\]

Univalence is also provable in the sense that a term of the type
\[\forall{\ell}{A B : Type \ell} \ra (A \equiv B) \simeq (A \simeq B)\]
can be constructed. For our purposes we actually only need half of this
equivalence: the very helpful
\[ua : {A B : Type} \ra A \simeq B \ra A \equiv B\]

Additionally, Cubical Agda's support for HITs and pattern matching on their
constructors will be very useful.

The benefit of all this is canonicity. Since $ua$ and HITs are non-axiomatic,
terms constructed by their use actually compute to a value. This means our
formalization actually computes the result of applying patches. Sadly, however,
this is not entirely true. There are two exceptions to this canonicity at the
time of writing:
\begin{enumerate}
\item $transp$ over indexed families, and
\item $hcomp$ over indexed families.
\end{enumerate}
