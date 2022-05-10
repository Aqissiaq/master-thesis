\section{Computational Results}\label{sec:results}

Having implemented several patch theories we can have a look at what they actually do.
In this section we do exactly that, considering some concrete examples of repositories,
patches and merges for the three [TWO IF RICHER DOESN'T WORK OUT] theories.

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
{-# OPTIONS --cubical --allow-unsolved-metas #-}
module results where
module _ where
  open import elementary-hpt
  open import Cubical.Data.Int
  open import Cubical.Data.Nat
  open import Cubical.Data.Sigma
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
  -- this takes 1m47s to typecheck
  -- _ : apply (addN 1000) 0 ≡ 1000
  -- _ = refl
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
module _ where
  open import laws-hpt-noTrunc-noIndep
  open import Cubical.Foundations.Prelude
    using(_∙_ ; refl ; sym ; _≡_ ; transportRefl ; fst ; _≡⟨_⟩_ ; _∎ ; cong)
  open import Cubical.Foundations.GroupoidLaws

  open import Data.Fin.Base
  open import Data.Nat.Properties.Core
  open import Relation.Nullary.Decidable.Core
  open import Agda.Builtin.Unit
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
