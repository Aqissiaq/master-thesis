\begin{code}[hide]
{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
\end{code}

\begin{frame}[fragile, allowframebreaks]
\frametitle{Higher Inductive Types}
\begin{itemize}
\item Custom groupoids
\item Quotients (and truncation)
\begin{code}
data _/_ (A : Type) (_∼_ : A → A → Type) : Type where
  [_] : A → A / _∼_
  eq : ∀ {a b} → a ∼ b → [ a ] ≡ [ b ]
  trunc : {a b : A / _∼_} → (p q : a ≡ b) → p ≡ q
\end{code}
\item Synthetic Topology
\begin{code}
data S¹ : Type where
  base : S¹
  loop : base ≡ base
\end{code}
\item Elimination
\begin{code}
reverse : S¹ → S¹
reverse base = base
reverse (loop i) = loop (~ i)
\end{code}
\end{itemize}
\end{frame}
