\section{An Elementary Patch Theory}\label{sec/elementary-hpt}

This section discusses the implementation of \emph{an elementary patch theory}
as described by section 4 of hpt~\cite{Angiuli2016}.
\begin{code}[hide]
{-# OPTIONS --cubical #-}

module elementary-hpt where

open import Function.Base
open import Data.Product
open import Cubical.Data.Int

open import Cubical.Core.Everything
  hiding (I)
open import Cubical.Foundations.Prelude public
  using (
    _≡_
  ; refl
  ; _∙_
  ; _≡⟨_⟩_
  ; _∎
  ; cong
  ; cong₂
  ; sym
  )

open import Cubical.Foundations.Univalence
  using (pathToEquiv)
\end{code}

\subsection{The Circle as a Repository}

In the elementary patch theory the repository is a single integer and there is exactly
one kind of patch: adding one to the integer.
This means the underlying type has one point constructor \texttt{num} and
one path \texttt{add1 : num ≡ num}.

The structure of this type may seem familiar - it is just the circle with its constructors renamed!
The cubical library already implements some HITs, including the circle so we will simply rename it and
its constructors.

In fact this implementation comes with a proof that the fundamental group of $S^1$ is the integers,
which contains many of the ingredients we will need. Specifically the loop space $ΩS^1$ is the type
of patches, and \texttt{helix : S¹ → Type} is precisely the interpretation of points in \texttt{R} as
types of repositories. Concretely \texttt{helix} maps \texttt{base} to the integers, and \texttt{loop}
to \texttt{ua} of the equivalence \texttt{ℤ ≃ ℤ} induced by the successor function.

\begin{code}
open import Cubical.HITs.S1.Base public
  renaming(
    S¹ to R
  ; base to num
  ; loop to add1
  ; ΩS¹ to Patch
  ; helix to I)
\end{code}

With this machinery we can easily define an interpretation of patches as bijections on \texttt{ℤ}
by applying \texttt{I} along the patch and weakening the resulting path. For convenience we also
define a function to apply a patch to a given integer.
\begin{code}
interp : Patch → ℤ ≃ ℤ
interp p = pathToEquiv (cong I p)

apply : Patch → ℤ → ℤ
apply p n = equivFun (interp p) n
\end{code}

\subsection{Merge}

Knowing that addition on the integers is commutative, merging two patches simply swaps
the order.

\begin{code}
merge : (Patch × Patch) → (Patch × Patch)
merge (p , q) = (q , p)
\end{code}

We now prove some properties of merge. Symmetry is essentially trivial, since swapping
the order twice gets us back to where we started.

\begin{code}
symmetric : { f1 f2 g1 g2 : Patch }
            → merge ( f1 , f2 ) ≡ ( g1 , g2 ) → merge ( f2 , f1 ) ≡ ( g2 , g1 )
symmetric p = cong merge p
\end{code}

Reconcile turns out to be more involved, but luckily some work is done for us.
It boils down to showing that composition of patches commutes, which relies on two facts:
\begin{enumerate}
  \item \texttt{intLoop} is a group homomorphism
  \item addition on the integers is commutative
\end{enumerate}

Both of these facts are in the standard library, so the task reduces to stitching them together.
First we convert the patches to explicit integers $n, m$ using the fact that \texttt{intLoop} is surjective.
We then apply the proof of commutativity for integers, and convert back to patches.

It is noteworthy that we were able to define \texttt{merge} without reference to explicit numbers,
but in order to prove its properties we require a "detour" into the integers.
\begin{code}
intLoop-sur : (p : Patch) → ∃[ n ] (p ≡ intLoop n)
intLoop-sur p = apply p 0 , sym (decodeEncode num p)

patch-comm : (p q : Patch) → p ∙ q ≡ q ∙ p
patch-comm p q = let (n , p-is-n) = intLoop-sur p
                     (m , q-is-m) = intLoop-sur q in
  p ∙ q ≡⟨ cong₂ _∙_ p-is-n q-is-m ⟩
  intLoop n ∙ intLoop m ≡⟨ intLoop-hom n m ⟩
  intLoop (n + m) ≡⟨ cong intLoop (+Comm n m) ⟩
  intLoop (m + n) ≡⟨ sym (intLoop-hom m n) ⟩
  intLoop m ∙ intLoop n ≡⟨ cong₂ _∙_ (sym q-is-m) (sym p-is-n) ⟩
  q ∙ p ∎
\end{code}

With the commutativity of patches established, reconcile follows easily:

\begin{code}
reconcile : {f1 f2 g1 g2 : Patch}
          → merge (f1 , f2) ≡ (g1 , g2) → f1 ∙ g1 ≡ f2 ∙ g2
reconcile p = let f1=g2 = cong snd p
                  g1=f2 = cong fst (sym p) in
  (cong₂ _∙_ f1=g2 g1=f2) ∙ (patch-comm _ _)
\end{code}
