\section{A Patch Theory With Richer Contexts}\label{sec:richer}
\begin{code}[hide]
{-# OPTIONS --cubical --rewriting #-}

module richer-no-laws where

open import indexing
open import vector-implementation

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Data.Fin
open import Data.String
  hiding (_<_)
\end{code}

The previous patch theories have both described repositories with a single context --
in which patches are always applicable. In this section we explore a theory with more
complex contexts by implementing Angiuli et al.'s \emph{Patch Theory With Richer Contexts}.

\subsection{The Type of Repositories}
The intended model for this theory is one where the patches either insert a string \texttt{s} on the
\texttt{l}th line (\texttt{ADD s AT l}), or remove the \texttt{l}th line (\texttt{RM l}).

Clearly these patches are not always applicable. It does not make sense to remove the 4th line of a file
with only 3 lines, nor to insert something on line 14 in the same context.
To incorporate this more complicated patch language, the repository type must also be more complicated.
This is accomplished by indexing \texttt{R} by a type
of patch histories, where \texttt{History m n} is the type of sequences of patches which takes an \texttt{m}-
line file to an \texttt{n}-line file.

\begin{code}
data History : ℕ → ℕ → Type where
  []         : {m : ℕ} → History m m
  ADD_AT_::_ : {m n : ℕ} (s : String) (l : Fin (suc n)) →
               History m n → History m (suc n)
  RM_::_     : {m n : ℕ} (l : Fin (suc n)) →
               History m (suc n) → History m n
\end{code}

It would also be possible to include higher constructers to specify patch laws,
but we refrain in order to simplify other developments.
\begin{code}
data R : Type where
  doc  : {n : ℕ} → History 0 n → R

  addP : {n : ℕ} (s : String) (l : Fin (suc n))
         (h : History 0 n) → doc h ≡ doc (ADD s AT l :: h)
  rmP  : {n : ℕ} (l : Fin (suc n))
         (h : History 0 (suc n)) → doc h ≡ doc (RM l :: h)
\end{code}

\begin{code}[hide]
mapSingl : {A B : Type} → (f : A → B) → {M : A} → singl M → singl (f M)
mapSingl f (x , p) = (f x) , (λ i → f (p i))

contrEquiv : {A B : Type} → (A → B) → isContr A → isContr B → A ≃ B
contrEquiv f (aCtr , aContr) contrB = isoToEquiv
  (iso f (λ _ → aCtr) (λ b → isContr→isProp contrB (f aCtr) b) aContr)

singl-biject : {A B : Type} {a : A} {b : B} → (singl a → singl b) → singl a ≃ singl b
singl-biject {a = a} {b = b} f = contrEquiv f (isContrSingl a) (isContrSingl b)
\end{code}

Another challenge with this richer theory is its interpretation. In the previous theories,
the context was modelled by a single type, and patches by an equivalence on this type.
In this setting we need a slightly different approach.

While it is natural to model a file of \text{n} lines as an \texttt{n}-vector of strings,
such a solution would lead to problems for patches. For example, \texttt{add s l []} would need
to be an equivalence of \texttt{Vec String 0} and \texttt{Vec String 1} which is not possible
since these types are not equivalent.

Instead we note that a history actually determines a particular vector (by \texttt{replay}), and use the singleton
type of this vector. Now, since any function between singletons determines a bijection (\texttt{singl-biject})
and a function on elements determines a function on singletons (\texttt{mapSingl}), it suffices to
define appropriate functions on vectors (\texttt{add} and \texttt{rm}) to obtain the needed equivalences.

\begin{code}
replay : {n : ℕ} → History 0 n → Vec String n
replay [] = []
replay (ADD s AT l :: h) = add s l (replay h)
replay (RM l :: h) = rm l (replay h)

Interpreter : R → Type
Interpreter (doc x) = singl (replay x)
Interpreter (addP s l h i) = ua (singl-biject {a = replay h} (mapSingl (add s l))) i
Interpreter (rmP l h i) = ua (singl-biject {a = replay h} (mapSingl (rm l))) i
\end{code}

\begin{code}[hide]
interp : {n1 n2 : ℕ} {h1 : History 0 n1} {h2 : History 0 n2} →
         doc h1 ≡ doc h2 → Interpreter (doc h1) ≃ Interpreter (doc h2)
interp p = pathToEquiv (cong Interpreter p)

apply : {n1 n2 : ℕ} {h1 : History 0 n1} {h2 : History 0 n2} →
        doc h1 ≡ doc h2 → Interpreter (doc h1) → Interpreter (doc h2)
apply p = equivFun (interp p)
\end{code}

\subsection{A Merge Function}

We now turn our attention to defining a merge function.
For this purpose we introduce an alternate interpreter which interprets repositories
not as vectors, but just as their history.
The purpose is to reduce the problem of defining the merge of patches to the problem
of defining a merge of histories.

\begin{code}
InterpreterH : R → Type
InterpreterH (doc x) = singl x
InterpreterH (addP s l h i) = ua (singl-biject {a = h} (mapSingl (ADD s AT l ::_))) i
InterpreterH (rmP l h i) = ua (singl-biject {a = h} (mapSingl (RM l ::_))) i

interpH : ∀ {n m}{h : History 0 n}{h' : History 0 m} → doc h ≡ doc h' → singl h ≃ singl h'
interpH p = (pathToEquiv (cong InterpreterH p))

applyH :{n1 n2 : ℕ} {h1 : History 0 n1} {h2 : History 0 n2} →
       doc h1 ≡ doc h2 → InterpreterH (doc h1) → InterpreterH (doc h2)
applyH p = equivFun (interpH p)
\end{code}

\begin{code}[hide]
_+++_ : {n1 n2 n3 : ℕ} → History n1 n2 → History n2 n3 → History n1 n3
h1 +++ [] = h1
h1 +++ (ADD s AT l :: h2) = ADD s AT l :: (h1 +++ h2)
h1 +++ (RM l :: h2) = RM l :: (h1 +++ h2)

+++-left-id : ∀ {n m} → (h : History n m) → ([] +++ h) ≡ h
+++-left-id [] = refl
+++-left-id (ADD s AT l :: h) = cong (ADD s AT l ::_) (+++-left-id h)
+++-left-id (RM l :: h) = cong (RM l ::_) (+++-left-id h)

+++-assoc : ∀ {n m k l}
            → (h1 : History n m)
            → (h2 : History m k)
            → (h3 : History k l)
            → (h1 +++ h2) +++ h3 ≡ (h1 +++ (h2 +++ h3))
+++-assoc h1 h2 [] = refl
+++-assoc h1 h2 (ADD s AT l :: h3) = cong (ADD s AT l ::_) (+++-assoc h1 h2 h3)
+++-assoc h1 h2 (RM l :: h3) = cong (RM l ::_) (+++-assoc h1 h2 h3)
\end{code}

Another issue is the following: when is a merge a meaningful operation?
To answer that question we introduce the concept of an extension. A history
\texttt{h2} is an extension of \texttt{h1} if \texttt{h2} has \texttt{h1} as
a prefix (there exists a \texttt{h3} such that \texttt{h1 +++ h3} is equal to \texttt{h2}).
\begin{code}
Extension : {n m : ℕ} → History 0 n → History 0 m → Type
Extension {n} {m} h1 h2 = Σ[ h3 ∈ History n m ] (h1 +++ h3) ≡ h2
\end{code}
Here \texttt{+++} denotes straight-forward concatenation of histories.

It is simple to turn a history into a path in \texttt{R} by using the constructors of \texttt{R},
and likewise to turn an extension into a path.
Note that \texttt{extToPath} actually ignores the extension
itself, instead computing the patch going "via" the empty file.
\begin{code}
toPath : {n : ℕ} (h : History 0 n) → doc [] ≡ doc h
toPath [] = refl
toPath (ADD s AT l :: h) = (toPath h) ∙ addP s l h
toPath (RM l :: h) = (toPath h) ∙ rmP l h

extToPath : {n m : ℕ} {h : History 0 n} {h' : History 0 m} →
            Extension h h' → doc h ≡ doc h'
extToPath {h = h} {h' = h'} _ = sym (toPath h) ∙ toPath h'
\end{code}
\begin{code}[hide]
emtpy-extension : ∀ {n} {h : History 0 n} → Extension h h
emtpy-extension = [] , refl
module merging {
\end{code}

This successfully reduces merging to a function on histories. Let us assume such a function:
\begin{code}
  mergeH : {n m : ℕ} →
           (h1 : History 0 n) (h2 : History 0 m) →
           Σ[ n' ∈ ℕ ] (Σ[ h' ∈ History 0 n' ] (Extension h1 h' × Extension h2 h'))
\end{code}
\begin{code}[hide]
  } where
\end{code}

We can then obtain histories through \texttt{InterpreterH}, apply the history merger,
and turn the resulting extensions back into paths.
\begin{code}
  merge : {n1 n2 : ℕ}{h1 : History 0 n1}{h2 : History 0 n2}
        → (doc [] ≡ doc h1) → (doc [] ≡ doc h2)
        → Σ[ n' ∈ ℕ ] (Σ[ h' ∈ History 0 n' ] (doc h1 ≡ doc h') × (doc h2 ≡ doc h'))
  merge p1 p2 = let (p1H , p1P) = applyH p1 ([] , refl)
                    (p2H , p2P) = applyH p2 ([] , refl)
                    (_ , (h' , ((ext1 , ext1-proof) , (ext2 , ext2-proof)))) = mergeH p1H p2H
                    e1 = ext1 , cong (_+++ ext1) p1P ∙ ext1-proof
                    e2 = ext2 , cong (_+++ ext2) p2P ∙ ext2-proof
    in (_ , (h' , extToPath e1 , extToPath e2))
\end{code}
