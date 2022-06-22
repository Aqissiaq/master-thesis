\begin{code}[hide]
{-# OPTIONS --cubical --rewriting --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Data.Fin
open import Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Data.String
open import laws-hpt-noTrunc-noIndep
  hiding(R ; opt ; optimize)
  renaming(GOAL1 to swapatNoop)
\end{code}

\begin{frame}[fragile]
\frametitle{A Theory with Laws}
\begin{itemize}
\item One context
\item One patch
\item Two patch laws
\end{itemize}
\begin{code}
data R : Type where
  doc : R
  _↔_AT_ : String → String → Fin size → doc ≡ doc
  noop : ∀ s i → s ↔ s AT i ≡ refl
  indep : ∀ s t u v i j → i ≢ j →
    (s ↔ t AT i) ∙ (u ↔ v AT j) ≡ (u ↔ v AT j) ∙ (s ↔ t AT i)
\end{code}
\end{frame}

\begin{code}[hide]
postulate
  swapatIndep : (s t u v : String) → (i j : Fin size) → i ≢ j
        → swapatPath (s , t) i ∙ swapatPath (u , v) j ≡ swapatPath (u , v) j ∙ swapatPath (s , t) i
\end{code}

\begin{frame}[fragile]
\frametitle{Model}
\begin{code}
Interp : R → Type
Interp doc = Vec String size
Interp ((s ↔ t AT idx) i) = ua (swapat (s , t) idx) i
Interp (noop s idx i j) = swapatNoop s idx i j
Interp (indep s t u v n m n≠m i j) =
  swapatIndep s t u v n m n≠m i j
\end{code}
\end{frame}

\begin{frame}[fragile]
\frametitle{A Patch Optimizer}
\begin{code}[hide]
postulate
  fooOpt :
\end{code}
\begin{itemize}
\item Program and prove
\begin{code}
    (p : doc ≡ doc) → Σ[ q ∈ doc ≡ doc ] p ≡ q
\end{code}
\item Pointwise
\begin{code}
  opt : (x : R) → Σ[ y ∈ R ] y ≡ x
\end{code}
\item Then apply with \texttt{λ p → cong opt p}
\item Patch laws are handled by contractibility of codomain
\end{itemize}
\end{frame}
