\begin{code}[hide]
{-# OPTIONS --cubical --rewriting --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Data.Fin
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Data.String
open import vector-implementation
\end{code}

\begin{frame}[fragile]
\frametitle{History}
\begin{code}
data History : ℕ → ℕ → Type where
  []         : {m : ℕ} → History m m
  ADD_AT_::_ : {m n : ℕ} (s : String) (l : Fin (suc n)) →
               History m n → History m (suc n)
  RM_::_     : {m n : ℕ} (l : Fin (suc n)) →
               History m (suc n) → History m n
\end{code}
\end{frame}

\begin{frame}[fragile]
\frametitle{The Theory}
\begin{code}
data R : Type where
  doc  : {n : ℕ} → History 0 n → R
  addP : {n : ℕ} (s : String) (l : Fin (suc n))
         (h : History 0 n) → doc h ≡ doc (ADD s AT l :: h)
  rmP  : {n : ℕ} (l : Fin (suc n))
         (h : History 0 (suc n)) → doc h ≡ doc (RM l :: h)
\end{code}
\end{frame}
\begin{code}[hide]
mapSingl : {A B : Type} → (f : A → B) → {M : A} → singl M → singl (f M)
mapSingl f (x , p) = (f x) , (λ i → f (p i))

contrEquiv : {A B : Type} → (A → B) → isContr A → isContr B → A ≃ B
contrEquiv f (aCtr , aContr) contrB = isoToEquiv
  (iso f (λ _ → aCtr) (λ b → isContr→isProp contrB (f aCtr) b) aContr)

singl-biject : {A B : Type} {a : A} {b : B} → (singl a → singl b) → singl a ≃ singl b
singl-biject {a = a} {b = b} f = contrEquiv f (isContrSingl a) (isContrSingl b)

\end{code}
\begin{frame}[fragile]
\frametitle{Model}
\begin{code}
replay : {n : ℕ} → History 0 n → Vec String n
replay [] = []
replay (ADD s AT l :: h) = add s l (replay h)
replay (RM l :: h) = rm l (replay h)

Interpreter : R → Type
Interpreter (doc x) = singl (replay x)
Interpreter (addP s l h i) =
  ua (singl-biject {a = replay h} (mapSingl (add s l))) i
Interpreter (rmP l h i) =
  ua (singl-biject {a = replay h} (mapSingl (rm l))) i
\end{code}
\end{frame}
