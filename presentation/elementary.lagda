\begin{code}[hide]
{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Int
open import Cubical.Data.Bool
\end{code}
\begin{frame}[fragile]
\frametitle{An Elementary Theory}
\begin{columns}
\begin{column}{.5\textwidth}
\begin{itemize}
  \item One context
  \item One patch
  \item Two models
\end{itemize}
\begin{code}
data R : Type where
  num : R
  patch : num ≡ num
\end{code}
\end{column}
\begin{column}{.5\textwidth}
\begin{code}
ℤI : R → Type
ℤI num = ℤ
ℤI (patch i) = sucPathℤ i

BI : R → Type
BI num = Bool
BI (patch i) = notEq i
\end{code}
\end{column}
\end{columns}
\end{frame}

\begin{code}[hide]
applyℤ : num ≡ num → ℤ → ℤ
applyℤ p n = equivFun (pathToEquiv (cong ℤI p)) n

applyB : num ≡ num → Bool → Bool
applyB p n = equivFun (pathToEquiv (cong BI p)) n
\end{code}

\begin{frame}[fragile]
\frametitle{In Practice}
\begin{code}
_ : applyℤ patch 0 ≡ 1
_ = refl

_ : applyB patch true ≡ false
_ = refl

_ : applyℤ (patch ∙ patch ∙ (sym patch)) 0 ≡ 1
_ = refl
\end{code}
\end{frame}
