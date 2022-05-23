\section{Computational Results}\label{sec:results}

Having implemented several patch theories we can have a look at what they actually do.
In this section we do exactly that, considering some concrete examples of repositories,
patches and merges for the three theories.

[NOTES]
\begin{itemize}
\item rewrite?
\item trans/hcomp problems
\item mention Brunerie number (and the smaller Brunerie nr.)
\end{itemize}

\subsection{Elementary Patch Computations}

First, consider the elementary patch theory implemented in \autoref{sec/elementary-hpt}.
Recall that this theory has one type of repositories -- the integers -- and one patch
-- \texttt{add1}.

\begin{code}[hide]
{-# OPTIONS --cubical --allow-unsolved-metas --rewriting #-}
module results where
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
  hiding(comp)
module _ where
  open import Cubical.Data.Int
  open import elementary-hpt
\end{code}

By the usual path operations we obtain some more patches: the "do nothing"-patch \texttt{noop},
the inverse \texttt{sub1} and compositions like \texttt{add2}.
\begin{code}
  noop sub1 add2 : Patch
  noop = refl
  sub1 = sym add1
  add2 = add1 ∙ add1
\end{code}

All of these suggestively named patches behave as one might expect:
\begin{code}
  _ : apply noop 1 ≡ 1
  _ = refl

  _ : apply add1 1 ≡ 2
  _ = refl

  _ : apply sub1 1 ≡ 0
  _ = refl

  _ : apply add2 1 ≡ 3
  _ = refl

  _ : apply (add1 ∙ sub1) 1 ≡ 1
  _ = refl
\end{code}

We can generalize further and create patches to add or subtract any integer,
and these also compute as expected.
\begin{code}
  -- maybe hide this definition
  addN : ℤ → Patch
  addN (pos zero) = noop
  addN (pos (suc n)) = add1 ∙ addN (pos n)
  addN (negsuc zero) = sub1
  addN (negsuc (suc n)) = sub1 ∙ addN (negsuc n)

  _ : apply (addN 22) 20 ≡ 42
  _ = refl

  _ : apply (addN (- 22)) 42 ≡ 20
  _ = refl
\end{code}

Clearly, this patch theory is a fully functioning calculator (for integer addition and subtraction),
but the detour through algebraic topology takes a computational toll.
The following proof typechecks, but it takes about 2 minutes.
\begin{code}
  _ : apply (addN 1000) 0 ≡ 1000
  _ = refl
\end{code}

\begin{figure}
\begin{centering}
\begin{tikzcd}
  & n \arrow[ld, "p"'] \arrow[rd, "q"] &\\
  x \arrow[rd, "p'"'] && y \arrow[ld, "q'"] \\
  & z&
\end{tikzcd}
\caption{\texttt{merger}}
\label{fig:elementary-merger}
\end{centering}
\end{figure}

Finally, we look at \texttt{merge}. The function \texttt{merger} neatly computes the result of
merging patches $p$ and $q$ from the original repository $n$ as shown in
\autoref{fig:elementary-merger}.
\begin{code}
  merger : ℤ → Patch → Patch → ℤ × ℤ
  merger n p q = let x = apply p n
                     y = apply q n
                     (p' , q') = merge (p , q)
    in (apply p' x , apply q' y)
\end{code}

Applying \texttt{merger} to a few test cases, it too behaves as expected.
The resulting two integers are always equal, which is exactly what we want merge to do.
Of course this is a consequence of the general case proven by \texttt{reconcile} in
\autoref{sec/elementary-hpt}, but it is good to see it in practice.
\begin{code}
  _ : merger 0 noop sub1 ≡ (-1 , -1)
  _ = refl

  _ : merger 0 (addN 5) (addN (-3)) ≡ (2 , 2)
  _ = refl
\end{code}

\subsection{Patch Computations with Laws}

Next we examine the patch theory with laws and its patch optimizer from \autoref{sec/laws-noTrunc-noIndep}.
In this theory the repository is a fixed-length vector of strings, and the patches permute the string
at a given index.
\begin{code}[hide]
open import Cubical.Foundations.Prelude
  hiding(comp)
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Vec
open import Data.Fin.Base
open import Data.Nat.Properties.Core
open import Relation.Nullary.Decidable.Core
open import Agda.Builtin.Unit

_∘_ : {A B C : Type} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

module _ where
  open import laws-hpt-noTrunc-noIndep
\end{code}

For concrete examples, consider the starting repository and patches:
\begin{code}
  repo : repoType
  repo = "hello" ∷ "world" ∷ []

  nop swap swap' comp : Patch
  nop = "nop" ↔ "nop" AT (# 0)
  swap = "hello" ↔ "greetings" AT (# 0)
  swap' = "world" ↔ "earthlings" AT (# 1)
  comp = swap ∙ swap'
\end{code}

When applying these patches, we encounter the current limits of Cubical Agda.
In particular, \texttt{Vec String size} is a dependent family so \texttt{transp} and
\texttt{hcomp} do not compute on it. In the simple case of applying just one patch the issue
is resolved by \texttt{transportRefl : (x : A) → transport refl x ≡ x}, giving the expected result.
\begin{code}
  _ : apply nop repo ≡ repo
  _ = transportRefl repo

  _ : apply swap repo ≡ "greetings" ∷ "world" ∷ []
  _ = transportRefl _
\end{code}

In the case of composition it gets more difficult. The following cannot be proven by
\texttt{transportRefl}, since the computation gets stuck on the composition.
\begin{code}
  _ : apply comp repo ≡ "greetings" ∷ "earthlings" ∷ []
  _ = {!!}
\end{code}

Of course it is possible to compute the result by hand. Here we have some more information
about the patches being composed, and are able to eliminate the composition before applying the patch.
\begin{code}
  _ : apply (nop ∙ swap) repo ≡  "greetings" ∷ "world" ∷ []
  _ = apply (nop ∙ swap) repo
    ≡⟨ cong (λ p → apply (p ∙ swap) repo) (R.noop "nop" (# 0)) ⟩
      apply (refl ∙ swap) repo
    ≡⟨ cong (λ p → apply p repo) (sym (lUnit swap)) ⟩
      apply swap repo
    ≡⟨ transportRefl _ ⟩ ("greetings" ∷ "world" ∷ []) ∎
\end{code}

Applying the patches in order also produces the expected result.
[THIS SHOULD BE EQUIVALENT TO COMPOSITION, BUT IT'S REALLY HAIRY]
\begin{code}
  _ : apply swap (apply swap' repo) ≡ "greetings" ∷ "earthlings" ∷ []
  _ = cong (apply swap) (transportRefl ("hello" ∷ "earthlings" ∷ [])) ∙ transportRefl _
\end{code}

In addition to the patches themselves this theory includes an optimizer
making use of the patch laws. In our implementation these optimized patches come equipped
with a proof that they are equal to the original patch, so testing the results should not reveal
anything new -- nevertheless it is interesting to note just how slow these computations are.

All three exhaust the heap, taking on the order of 10s of minutes to do so, \texttt{swapOpt} is
particularly notable since \texttt{optimize} does not actually do anything.
The strings in \texttt{swap} are not equal, and so the patch should be kept as it is.
\begin{code}
  nopOpt swapOpt compOpt : Patch
  nopOpt = fst (optimize nop)
  swapOpt = fst (optimize swap)
  compOpt = fst (optimize comp)

  -- _ : apply swapOpt repo ≡ "greetings" ∷ "world" ∷ []
  -- _ = transportRefl "greetings" ∷ "world" ∷ []

  -- _ : apply nopOpt repo ≡ repo
  -- _ = transportRefl repo

  -- _ : apply compOpt repo ≡ "greetings" ∷ "earthlings" ∷ []
  -- _ = transportRefl _
\end{code}

\subsection{Richer Contexts}

\begin{code}[hide]
module richer where
  open import richer-no-laws public

  S : {A : Type} → (x : A) → singl x
  S x = x , refl
\end{code}
Finally, we consider the patch theory with richer contexts from \autoref{sec:richer}.
For this theory we have implemented two interpretations, we will look at them in turn
followed by merging. For the purpose of testing, define a few simple patches:
\begin{code}
  addPatch : doc [] ≡ doc (ADD "hello" AT zero :: [])
  addPatch = addP "hello" zero []

  rmPatch : doc (ADD "hello" AT zero :: []) ≡ doc (RM zero :: (ADD "hello" AT zero :: []))
  rmPatch = rmP zero (ADD "hello" AT zero :: [])
\end{code}

\subsubsection{Vector Interpretation}

The first interpretation sends each \texttt{doc h} to a singleton type of the vector determined
by replay. For the simplest patches this works as expected with \texttt{transportRefl}.
(Here \texttt{S} denotes the inclusion into the singleton type.)

\begin{code}
  _ : apply addPatch (S []) ≡ S ("hello" ∷ [])
  _ = transportRefl _

  _ : apply rmPatch (S ("hello" ∷ [])) ≡ S []
  _ = transportRefl _

  _ : apply rmPatch (apply addPatch (S [])) ≡ S []
  _ = cong (apply rmPatch) (transportRefl ("hello" ∷ [] , refl))
      ∙ (transportRefl ([] , refl))
\end{code}

Again, direct composition of patches runs in to the current limits of Cubical Agda.
Because \texttt{hcomp} does not reduce in singletons (which is a $\Sigma$-type),
we get stuck trying to compute the (enormous) composition term.
\begin{code}
  -- _ : apply (addPatch ∙ rmPatch) (S []) ≡ S []
  -- _ = apply (addPatch ∙ rmPatch) (S (replay []))
  --   ≡⟨ transportRefl _ ⟩ _
  --   ≡⟨ {!!} ⟩ S (replay (RM zero :: (ADD "hello" AT zero :: []))) ∎
\end{code}

\subsubsection{History Interpretation}

The second interpretation eludes replaying the patches, instead sending \texttt{doc h}
to the singleton history \texttt{h}. In a familiar turn of events the simple patches give
expected results, but composition poses a problem. (Note that \texttt{[]} in these examples
is the empty \emph{history} rather than the empty vector.)

\begin{code}
  _ : applyH addPatch (S []) ≡ S (ADD "hello" AT zero :: [])
  _ = transportRefl _

  _ : applyH rmPatch (S (ADD "hello" AT zero :: []))
    ≡ S (RM zero :: (ADD "hello" AT zero :: []))
  _ = transportRefl _
\end{code}

\subsubsection{Merge}
\begin{code}[hide]
  undo : ∀ {n m} → History n m → History m n
  undo [] = []
  undo (ADD s AT l :: h) = (RM l :: []) +++ (undo h)
  undo (RM l :: h) = (ADD "uh oh" AT l :: []) +++ undo h

  postulate
    undo-inverse : ∀ {n m} → (h : History n m)
                   → h +++ undo h ≡ []
\end{code}

In \autoref{sec:richer} we reduced the task of merging patches to merging histories.
As a concrete example, consider a merger of histories which keeps one history if the other is empty,
but simply undos the changes in both branches if there is a possibility of conflict.
\begin{code}
  undo-merge : {n m : ℕ} →
               (h1 : History 0 n) (h2 : History 0 m) →
               Σ[ n' ∈ ℕ ] (Σ[ h' ∈ History 0 n' ] (Extension h1 h' × Extension h2 h'))
  undo-merge {_} {m} [] h2 = m , h2 , (h2 , +++-left-id h2) , ([] , refl)
  undo-merge {n} {_} h1 [] = n , h1 , ([] , refl) , (h1 , +++-left-id h1)
  undo-merge {_} {_} h1 h2 = 0 , [] , (undo h1 , undo-inverse h1) , (undo h2 , undo-inverse h2)
  open merging {undo-merge}
\end{code}

We further define some simple patches
\begin{code}
  p1 : doc [] ≡ doc (ADD "hello" AT zero :: [])
  p1 = addP "hello" (zero) []

  p2 : doc (ADD "hello" AT zero :: []) ≡ doc (ADD "world" AT suc zero :: (ADD "hello" AT zero :: []))
  p2 = addP "world" (suc zero) (ADD "hello" AT zero :: [])
\end{code}

and observe that the merged histories (or at least their lengths) give the expected
results by \texttt{transportRefl}. Merging \texttt{p1} with \texttt{refl} keeps \texttt{p1}:
\begin{code}
  _ : fst (merge refl p1) ≡ 1
  _ = fst (undo-merge (fst (applyH refl ([] , refl))) ((fst (applyH p1 ([] , refl)))))
    ≡⟨ cong {y = []} (λ x → fst (undo-merge x (fst (applyH p1 ([] , refl))))) (transportRefl _) ⟩
      fst (undo-merge [] ((fst (applyH p1 ([] , refl)))))
    ≡⟨ cong {y = ADD "hello" AT zero :: []} (λ x → fst (undo-merge [] x)) (transportRefl _) ⟩
      fst (undo-merge [] (ADD "hello" AT zero :: [])) ∎
\end{code}

Merging two non-empty patches results int he empty patch:
\begin{code}
  _ : fst (merge p1 p1) ≡ 0
  _ = fst (undo-merge (fst (applyH p1 ([] , refl))) ((fst (applyH p1 ([] , refl)))))
    ≡⟨ cong {y = (ADD "hello" AT zero :: [])}
            (λ x → fst (undo-merge x (fst (applyH p1 ([] , refl))))) (transportRefl _) ⟩
       fst (undo-merge (ADD "hello" AT zero :: []) (fst (applyH p1 ([] , refl))))
    ≡⟨ cong {y = (ADD "hello" AT zero :: [])}
            (λ x → fst (undo-merge  (ADD "hello" AT zero :: []) x)) (transportRefl _) ⟩
       fst (undo-merge (ADD "hello" AT zero :: []) (ADD "hello" AT zero :: [])) ∎
\end{code}

Finally we note that composition does not pose a problem here, since \texttt{undo-merge}
extracts the history and does not need to compute the actual composition of patches.
\begin{code}
  _ : fst (merge (p1 ∙ p2) refl) ≡ 2
  _ = fst (undo-merge (fst (applyH (p1 ∙ p2) ([] , refl))) ((fst (applyH refl ([] , refl)))))
    ≡⟨ cong {y = []} (λ x → fst (undo-merge (fst (applyH (p1 ∙ p2) ([] , refl))) x)) (transportRefl _) ⟩
      fst (undo-merge (fst (applyH (p1 ∙ p2) ([] , refl))) [])
    ≡⟨ cong {y = ADD "world" AT (suc zero) :: transport refl (ADD "hello" AT zero :: transport refl [])}
            (λ x → fst (undo-merge x [])) (transportRefl _) ⟩
      fst (undo-merge (ADD "world" AT (suc zero) :: transport refl (ADD "hello" AT zero :: transport refl [])) [])
    ≡⟨ cong {y = ADD "hello" AT zero :: []}
            (λ x → fst (undo-merge (ADD "world" AT suc zero :: x) [])) (transportRefl _) ⟩
      fst (undo-merge (ADD "world" AT (suc zero) :: (ADD "hello" AT zero :: [])) []) ∎
open richer
\end{code}
