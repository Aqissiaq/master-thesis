\section{A Patch Theory With Laws}\label{sec/laws-noTrunc-noIndep}

In this section we explore a formalization of HPTs section 5: \textbf{A Patch Theory with Laws}.
This is a more complicated patch theory in which the type \texttt{R} has not only repositories
and patches, but also a patch \emph{law} represented by a square (a path between path).

We start by implementing the patch theory, followed by a "patch optimizer" that computes
smaller patches with the same effect. This optimizer makes crucial use of the patch law.

\begin{code}[hide]
{-# OPTIONS --cubical #-}

module laws-hpt-noTrunc-noIndep where

open import Data.Fin public
  using(Fin  ; #_ ; zero ; suc)
open import Data.String
  using(String ; _≟_ ; _==_)
open import Data.Vec public
  using(Vec ; [] ; _∷_ ; _[_]%=_ ; updateAt)
open import Data.Empty
  using(⊥ ; ⊥-elim)

open import Cubical.Core.Everything
  hiding (I)
open import Cubical.Foundations.Prelude
  renaming (I to Interval)
open import Cubical.Data.Equality
  hiding (I)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
  hiding (I)
open import Cubical.Data.Bool
  hiding(_≟_)
open import Cubical.Data.Nat.Order
  hiding(_≟_)
open import Function.Base
  using(id ; _∘_ )
open import Relation.Nullary
open import Relation.Binary
  using (Decidable)

open import Cubical.Foundations.HLevels

open import path-transport
  renaming (x=a to path-transport-lemma)

open import Cubical.Foundations.Everything
  hiding(_∘_ ; I ; id)


_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≢_ x y = x ≡ y → ⊥

sym≢ : ∀ {ℓ} {A : Set ℓ} → {x y : A}
       → x ≢ y → y ≢ x
sym≢ x≢y x≡y = ⊥-elim (x≢y (sym x≡y))

_=?_ : Decidable _≡p_
_=?_ = _≟_

size : ℕ
size = 2
\end{code}

\subsection{The Patch Theory}

In this patch theory we consider repositories consisting of a single file with lines of text.
There is one type of patch which permutes the line at a given index. Let \texttt{Patch} denote the type
\texttt{doc ≡ doc}.

Additionally we enforce a patch \emph{law} with the \texttt{noop} constructor which states that
swapping a string for itself is the same as doing nothing.

In the geometric interpretation of HITs this is a space with one point, loops for each choice of
\texttt{(s1, s2, i)} and a cylinder between each loop where \texttt{s1 == s2} and the constant path.

\begin{code}
data R : Type where
  doc : R
  _↔_AT_ : (s1 s2 : String) (i : Fin size) → (doc ≡ doc)
  noop : (s : String) (i : Fin size) → s ↔ s AT i ≡ refl
\end{code}
\begin{code}[hide]
Patch : Type
Patch = doc ≡ doc
\end{code}
\begin{code}[hide]
postulate
\end{code}
Angiuli et al's original definition also includes an additional law:
\begin{code}
  indep : (s t u v : String) (i j : Fin size) → (i ≢ j) →
          (s ↔ t AT i) ∙ (u ↔ v AT j)
        ≡ (u ↔ v AT j) ∙ (s ↔ t AT i)
\end{code}

This law states that swapping strings commutes as long as the indices are different.
We do not include this law as it leads to some problems later. See \autoref{subsec/opt}.

In order to interpret this model in the universe of types (called \texttt{Type} in Cubical Agda)
we will need three things:
\begin{enumerate}
  \item a \emph{type} of repository contexts \texttt{repoType},
  \item a path \texttt{swap} from \texttt{repoType} to itself for
        each choice of strings and index, and
  \item a path of paths between \texttt{swap s s i} and \texttt{refl}
\end{enumerate}

The type of repositories will be realized by vectors of strings of a fixed size.
\begin{code}
repoType : Type
repoType = Vec String size
\end{code}

To create a path \texttt{swap s1 s2 i : repoType ≡ repoType} we will first construct an
isomorphism and then use \texttt{ua} to make a path in the universe.

Semantically, our patch should swap the line at index \texttt{j} if it is equal to either \texttt{s1}
or \texttt{s2} and otherwise leave it alone. This behavior is encoded in \texttt{permute} and \texttt{permuteAt}
applies it to the appropriate index.

\begin{code}
permute : (String × String) → String → String
permute (s1 , s2) s with s =? s1 | s =? s2
...                    | yes _  | _     = s2
...                    | no _   | yes _ = s1
...                    | no _   | no _  = s

permuteAt : String → String → Fin size → repoType → repoType
permuteAt s t j = _[ j ]%= (permute (s , t))
\end{code}

To show that \texttt{permuteAt} is an isomorphism (and hence an equivalence) we need
some additional results.

First we show that updating at the same index twice is equal to updating once with the
composition of the functions.

\begin{code}
[]%=twice : ∀ {n} {A : Type₀} (f : A → A) (v : Vec A n) (i : Fin n)
            → (v [ i ]%= f [ i ]%= f) ≡ (v [ i ]%= f ∘ f)
\end{code}
\begin{code}[hide]
[]%=twice f (x ∷ xs) zero = refl
[]%=twice f (x ∷ xs) (suc i) = cong (x ∷_) ([]%=twice f xs i)
\end{code}
Then we show that updating by the identity function does not change the vector.
\begin{code}
[]%=id : ∀ {n} {v : Vec String n} {j : Fin n} → v [ j ]%= id ≡ v
\end{code}
\begin{code}[hide]
[]%=id {n} {x ∷ xs} {zero}  = refl
[]%=id {n} {x ∷ _} {suc j} = cong (x ∷_) []%=id
\end{code}

Both are proven by induction on the index.

\begin{code}[hide]
permuteTwice' : {s1 s2 : String} → (s : String)
                → permute (s1 , s2) (permute (s1 , s2) s) ≡ id s
permuteTwice' {s1} {s2} s with s =? s1 | s =? s2
...                       | yes s=s1 | _
                            with s2 =? s1 | s2 =? s2
...                         | yes s2=s1   | _        = ptoc s2=s1 ∙ sym (ptoc s=s1)
...                         | no _        | yes _    = sym (ptoc s=s1)
...                         | no _        | no s2≠s2 = ⊥-elim (s2≠s2 reflp)
permuteTwice' {s1} {s2} s | no _ | yes s=s2
                            with s1 =? s1 | s1 =? s2
...                         | yes _       | _        = sym (ptoc s=s2)
...                         | no s1≠s1    | _        = ⊥-elim (s1≠s1 reflp)
permuteTwice' {s1} {s2} s | no s≠s1 | no s≠s2
                            with s =? s1  | s =? s2
...                         | yes s=s1    | _        =  ⊥-elim (s≠s1 s=s1)
...                         | no _        | yes s=s2 =  ⊥-elim (s≠s2 s=s2)
...                         | no _        | no _     = refl
\end{code}

Finally, permuting twice is equivalent to the identity function.
The pointwise result \texttt{permuteTwice' : ∀ x → permute (s , t) (permute (s , t) x) ≡ id x}
is straightforwardly (but laboriously) proven by case analysis, from which the full result follows
by function extensionality.

\begin{code}
permuteTwice : ∀ {s t} → (permute (s , t) ∘ permute (s , t)) ≡ id
permuteTwice = funExt permuteTwice'
\end{code}

With these facts it follows that permuting at an index is its own inverse, and
an equivalence \texttt{swapat} can be constructed from this isomorphism.
\begin{code}
permuteAtTwice : ∀ s t j v → permuteAt s t j (permuteAt s t j v) ≡ v
permuteAtTwice s t j v = permuteAt s t j (permuteAt s t j v)
        ≡⟨ []%=twice (permute (s , t)) v j ⟩
          v [ j ]%= permute (s , t) ∘ permute (s , t)
        ≡⟨ cong (v [ j ]%=_) permuteTwice ⟩
          v [ j ]%= id
        ≡⟨ []%=id ⟩ v ∎

swapat : (String × String) → Fin size → repoType ≃ repoType
swapat (s , t) j = isoToEquiv
  (iso (permuteAt s t j) (permuteAt s t j) (permuteAtTwice s t j) (permuteAtTwice s t j))
\end{code}

For the \texttt{noop} law we need to show that \texttt{swapat} respects it.
We proceed in two steps. First \texttt{swapssId} shows that the underlying function of the equivalence
\texttt{swapat (s , s) j} is the identity function. Then, since two equivalences are equal if their
underlying functions are equal we get an identification of \texttt{swapat (s , s) j} and the identity equivalence.

\begin{code}[hide]
permuteId' : {s : String} → (t : String) → permute (s , s) t ≡ id t
permuteId' {s} t with t =? s | t =? s
...               | yes t=s | yes _   = sym (ptoc t=s)
...               | yes _   | no _    = refl
...               | no t≠s  | yes t=s = ⊥-elim (t≠s t=s)
...               | no _    | no _  = refl

permuteId : {s : String} → permute (s , s) ≡ id
permuteId {s} = funExt (permuteId' {s})
\end{code}
\begin{code}
swapssId : {s : String} {j : Fin size} → equivFun (swapat (s , s) j) ≡ idfun (repoType)
swapssId {s} {j} = funExt pointwise
  where
    pointwise : (r : repoType) → equivFun (swapat (s , s) j) r ≡ idfun repoType r
    pointwise r = equivFun (swapat (s , s) j) r ≡⟨ cong (λ x → r [ j ]%= id x) permuteId ⟩
                  r [ j ]%= id                  ≡⟨ []%=id ⟩
                  id r ∎

swapatIsId : {s : String} {j : Fin size} → swapat (s , s) j ≡ idEquiv repoType
swapatIsId = equivEq swapssId
\end{code}

With these pieces we are ready to interpret the repository HIT.
\texttt{I} sends \texttt{doc} to the type of string vectors, each patch to \texttt{ua} of the
\texttt{swapat} equivalence and each \texttt{noop} square to \texttt{swapatIsId} composed with
\texttt{uaIdEquiv} which is the path identifying \texttt{ua (idEquiv \_)} and \texttt{refl}.

Then we can interpret and apply patches like before.
\begin{code}
I : R → Type₀
I doc = repoType
I ((s1 ↔ s2 AT j) i) = ua (swapat (s1 , s2) j) i
I (noop s j i i') = (cong ua (swapatIsId {s} {j}) ∙ uaIdEquiv) i i'

interp : Patch → repoType ≃ repoType
interp p = pathToEquiv (cong I p)

apply : Patch → repoType → repoType
apply p = equivFun (interp p)
\end{code}

\subsection{A Patch Optimizer}\label{subsec/opt}

With the patch theory above it is possible to implement a patch optimizer --
a function that takes a patch and produces a new (hopefully smaller) patch
with the same effect. The development makes use of the \texttt{noop} patch law.

Specifically we implement the \emph{program and prove} approach from section 5.3 of HPT~\cite{Angiuli2016}.
With this approach we produce a function of type \texttt{(p : Patch) → $\Sigma_\texttt{(q : Patch)}$ p ≡ q}.
The result is a patch \texttt{q}, along with a proof that \texttt{q} is equal to the original patch.

We proceed in two steps. First creating a function
\begin{code}
opt : (x : R) → Σ[ y ∈ R ] y ≡ x
\end{code}
that performs the desired optimization on points, and then applying it along
a patch with \texttt{cong}.

The point constructor \texttt{doc} gets mapped to itself along with \texttt{refl}.
This is natural since we want to optimize patches and leave the repositories unchanged.
\begin{code}
opt doc = (doc , refl)
\end{code}
The path constructor \texttt{s1 ↔ s2 AT j} is where we implement our optimization.
If the two strings are different, we do nothing. Note that \texttt{x} here captures the
interval parameter, so that \texttt{(x , refl)} may be a point along the path.

If the strings \emph{are} equal we replace the patch with \texttt{refl$_\texttt{doc}$} by
mapping to \texttt{doc} regardless of the interval parameter. Now, our result type also requires
a proof that \texttt{refl} is in fact equal to permuting two equal strings and we have exactly
what we need: it's \texttt{noop}!

There are two complications. Firstly \texttt{noop} requires a swap-patch with identical strings.
Luckily we can use the proof that they are equal to get a patch of the correct type.
Secondly the \texttt{noop} square goes the wrong way -- from the patch to \texttt{refl} --
but this is easily fixed by inverting one interval argument.
\begin{code}
opt x@((s1 ↔ s2 AT j) i) with s1 =? s2
...                       | yes s1=s2 = doc
                                      , λ k → ((cong (_↔ s2 AT j) (ptoc s1=s2) ∙ noop s2 j) (~ k) i)
...                       | no _ = x , refl
\end{code}

For the \texttt{noop} constructor we make use of the fact that our codomain is
contractible. Since we are mapping into a contractible type (and hence a Set) we know
that all paths are equal, and can construct a square with sides matching the paths above.

However, since the sides must be \emph{definitionally} equal in Cubical Agda we employ
a trick from the set-truncation HIT elimination rule in the Cubical library. \texttt{isOfHLevelDep 2}
is the dependent version of \texttt{isSet}. We can then provide the sides
\texttt{cong opt (s ↔ s AT j)} and \texttt{refl} (or really \texttt{cong opt refl}). Since we are
constructing a \emph{dependent} square we also need a family of types \texttt{I → I → Type}, but this
is exactly what \texttt{noop s j} is!

\begin{code}
opt (noop s j i k) = isOfHLevel→isOfHLevelDep 2
  (isProp→isSet ∘ isContr→isProp ∘ result-contractible)
  _ _ (cong opt (s ↔ s AT j)) refl (noop s j) i k
\end{code}
\begin{code}[hide]
  where
\end{code}

Contractibility of the result type is immediate from the characterization of paths
in $\Sigma$-types and the inverse of the provided path.
\begin{code}
  result-contractible : {X : Type} → (x : X) → isContr (Σ[ y ∈ X ] y ≡ x)
  result-contractible x = (x , refl) , (λ (_ , p) → ΣPathP (sym p , λ i j → p (~ i ∨ j)))
\end{code}

This trick is the reason \texttt{indep} was left out. Because we need to apply \texttt{opt} to
the paths to compute the sides of the square it would not terminate, instead constructing squares
back and forth between \texttt{(s ↔ t AT i) ∙ (u ↔ v AT j)} and \texttt{(u ↔ v AT j) ∙ (s ↔ t AT i)}
for eternity.

There is one additional complication: The result of \texttt{cong opt p} for some patch \texttt{p}
is actually of type \texttt{Pathover (λ x → $\Sigma_\texttt{(y : R)}$ y ≡ x) p (doc,refl) (doc,refl)}.
Luckily this type is equivalent to our desired target type by:

\begin{code}
e : {p : Patch} →
    (PathP (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl) (doc , refl))
    ≡ (Σ[ q ∈ Patch ] p ≡ q)
\end{code}
\begin{code}[hide]
e {p} =
\end{code}
We present the (somewhat involved) proof here.
By the characterizations of paths over constant families and paths in $\Sigma$-types the Pathover
is equivalent to \texttt{$\Sigma_\texttt{q : Patch}$ (transport $^{x \mapsto (x ≡ \texttt{doc})}$ p) ≡ refl}.

\begin{code}
  (PathP (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl) (doc , refl))
    ≡⟨ PathP≡Path (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl) (doc , refl) ⟩
  Path (Σ[ y ∈ R ] y ≡ doc) (transport (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl)) (doc , refl)
    ≡⟨ cong (λ x → Path (Σ[ y ∈ R ] y ≡ doc) x (doc , refl)) (ΣPathP (refl , sym (lUnit p))) ⟩
  Path (Σ[ y ∈ R ] y ≡ doc) (doc , p) (doc , refl)
    ≡⟨ sym ΣPath≡PathΣ ⟩
  (Σ[ q ∈ Patch ] (PathP (λ i → q i ≡ doc) p refl))
    ≡⟨ Σ-cong-snd (λ q → PathP≡Path (λ i → q i ≡ doc) p refl) ⟩
  (Σ[ q ∈ Patch ] (transport (λ i → q i ≡ doc) p) ≡ refl)
\end{code}
Then we apply lemma 2.11.2 from the book
\footnote{For the category theorist: this is the functorial action of the contravariant hom-functor~\cite{hottbook}}
to obtain the $\Sigma$-type of patches \texttt{q} and proofs that $q^{-1} \cdot p \equiv \texttt{refl}$.
The proof by path induction was written for this purpose and has been contributed to the Cubical library.
\begin{code}[hide]
    ≡⟨ refl ⟩
\end{code}
\begin{code}
  (Σ[ q ∈ Patch ] (transport (λ i → q i ≡ doc) p) ≡ refl)
    ≡⟨ Σ-cong-snd (λ q → cong (_≡ refl) (path-transport-lemma q p)) ⟩
  (Σ[ q ∈ Patch ] (sym q ∙ p) ≡ refl)
\end{code}
\begin{code}[hide]
    ≡⟨ refl ⟩
\end{code}
We reach the desired type by the groupoid properties of path composition.
\begin{code}
  (Σ[ q ∈ Patch ] (sym q ∙ p) ≡ refl)
    ≡⟨ Σ-cong-snd (λ q → invLUnique q p) ⟩
  (Σ[ q ∈ Patch ] p ≡ q) ∎
\end{code}
In particular, \texttt{invLUnique} identifies $p^{-1} \cdot q \equiv \texttt{refl}$
with $q \equiv p$. The proof is by path induction and application of groupoid laws.
\begin{code}[hide]
  where
  invLUnique : {X : Type} {x y : X} →
               (p q : x ≡ y) → (sym p ∙ q ≡ refl) ≡ (q ≡ p)
  invLUnique {X} {x} = J P r
    where
    P : (y' : X) → x ≡ y' → Type _
    P y' p' = (q' : x ≡ y') → (sym p' ∙ q' ≡ refl) ≡ (q' ≡ p')

    r : P x refl
    r q' = sym refl ∙ q' ≡ refl
      ≡⟨ cong (λ p → p ∙ q' ≡ refl) symRefl ⟩ refl ∙ q' ≡ refl
      ≡⟨ sym (cong (_≡ refl) (lUnit q')) ⟩ (q' ≡ refl) ∎
\end{code}

Finally, \texttt{optimize} can be implemented as discussed -- by applying \texttt{opt} and
transporting along \texttt{e}.

\begin{code}
optimize : (p : Patch) → Σ[ q ∈ Patch ] p ≡ q
optimize p = transport e (cong opt p)
\end{code}
