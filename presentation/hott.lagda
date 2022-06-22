
\begin{code}[hide]
{-# OPTIONS --without-K #-}
open import Agda.Primitive renaming (Set to Type)
open import Data.Nat
open import Data.Char

\end{code}
% do all this in Agda syntax, we don't need translation
\begin{frame}[fragile]
\begin{itemize}
\frametitle{Types}
\item Types and terms
\begin{code}
naturals : Type
naturals = ℕ

aNumber : naturals
aNumber = 3
\end{code}
\item Elimination
\begin{code}
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))
\end{code}
\item (Inductive) type families
\begin{code}
data List (A : Type) : Type where
   []l  : List A
   _∷l_ : A → List A → List A
\end{code}
\end{itemize}
\end{frame}

\begin{frame}[fragile, allowframebreaks]
\frametitle{Dependent Types}
\begin{itemize}
\item A type that \emph{depends} on a term
\begin{code}
data Vec (A : Type) : ℕ → Type where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
\end{code}
\item Dependent elimination
\begin{code}
map : ∀ {A B n} → (A → B) → Vec A n → Vec B n
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs
\end{code}
\begin{code}[hide]
Vec-induction :
  {A : Type} → {P : ∀ {n} → Vec A n → Type} →
  (P []) →
  (∀ {n} → (a : A) → (as : Vec A n) → P (a ∷ as)) →
  {n : ℕ} → (v : Vec A n) → P v
-------------------------------------------------
Vec-induction empty _ [] = empty
Vec-induction _ cons (a ∷ v) = cons a v
\end{code}
\item $\Pi$-types
\begin{code}
Π : (X : Type) → (X → Type) → Type
Π X P = (x : X) → P x

countDown : Π ℕ (Vec ℕ)
countDown zero = []
countDown (suc x) = x ∷ (countDown x)
\end{code}
\item $\Sigma$-types
\begin{code}
record Σ (X : Type) (P : X → Type) : Type where
  constructor _,_
  field
    fst : X
    snd : P fst

_ : Σ ℕ (Vec ℕ)
_ = 2 , (0 ∷ (1 ∷ []))
\end{code}
\end{itemize}
\end{frame}

\begin{frame}[fragile, allowframebreaks]
\frametitle{Identity Types}
\begin{itemize}
\item When are two terms the same?
\begin{code}
data Id {X : Type} (x : X) : X → Type where
  refl : Id x x

_ : Id (double 2) 4
_ = refl

\end{code}
\item The J rule (identity induction)
\begin{code}
J : {X : Type} {x : X} →
    (P : (y : X) → (Id x y) → Type) →
    (base : P x refl) →
    -------------------------------------
    (y : X) → (p : Id x y) → P y p
\end{code}
\begin{code}[hide]
J P base y refl = base
module _ (X : Type) (x y z : X) where
\end{code}
\item Some properties
\begin{code}
  sym : Id x y → Id y x
  sym = J (λ y' p → Id y' x) refl y

  _∙_ : Id x y → Id y z → Id x z
  _∙_ p = J (λ z' q → Id x z') p z
\end{code}
\end{itemize}
\end{frame}

%\begin{frame}
%\frametitle{Cubical? ua?}
%\end{frame}
%
%\begin{frame}
%\frametitle{Interpretations (props, spaces)}
%\end{frame}

