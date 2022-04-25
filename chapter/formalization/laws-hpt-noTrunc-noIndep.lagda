\section{A Patch Theory With Laws}\label{sec/laws-noTrunc-noIndep}

\begin{code}[hide]

{-# OPTIONS --cubical --rewriting #-}

module laws-hpt-noTrunc-noIndep where

open import Data.Fin
  using(Fin  ; #_ ; zero ; suc)
open import Data.String
  using(String ; _≟_ ; _==_)
open import Data.Vec
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
size = 8
\end{code}

\subsection{The Patch Theory}

In this patch theory we consider repositories consisting of a single file with lines of text.
There is one type of patch which permutes the line at a given index.

Additionally we enforce patch \emph{laws} with the \texttt{noop} constructor which states that
swapping a string for itself is the same as doing nothing.

In the geometric interpretation of HITs this is a space with one point, loops for each choice of
\texttt{(s1, s2, i)} and a square between each loop where \texttt{s1 == s2} and the constant path.
\begin{code}
data R : Type₀ where
  doc : R
  _↔_AT_ : (s1 s2 : String) (i : Fin size) → (doc ≡ doc)
  noop : (s : String) (i : Fin size) → s ↔ s AT i ≡ refl
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
We do not include this law as it leads to some problems later. [SEE WHEREVER WE DISCUSS THAT]

In order to interpret this model in the universe of types we will need three things:
\begin{enumerate}
  \item a \emph{type} of repository contexts \texttt{repoType},
  \item a path \texttt{swap} from \texttt{repoType} to itself for
        each choice of strings and index, and
  \item a path of paths between \texttt{swap s s i} and \texttt{refl}
\end{enumerate}

The type of repositories will be realized by vectors of strings of a fixed size.
\begin{code}
repoType : Type₀
repoType = Vec String size
\end{code}

To create a path \texttt{swap s1 s2 i : repoType ≡ repoType} we will first construct a
bijection, and then use \texttt{ua} to make a path in the universe.

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
To show that \texttt{permuteAt} is a bijection (and hence an equivalence) we need
some additional results.

First we show that updating at the same index twice is equal to updating once with the
composition of the functions.
\begin{code}
[]%=twice : ∀ {n} {A : Type₀} (f : A → A) (v : Vec A n) (i : Fin n)
            → v [ i ]%= f [ i ]%= f ≡ v [ i ]%= f ∘ f
\end{code}
\begin{code}[hide]
[]%=twice f (x ∷ xs) zero = refl
[]%=twice f (x ∷ xs) (suc i) = cong (λ v → x ∷ v) ([]%=twice f xs i)
\end{code}
Then we show that updating by the identity function does not change the vector.
\begin{code}
[]%=id : ∀ {n} {v : Vec String n} {j : Fin n} → v [ j ]%= id ≡ v
\end{code}
\begin{code}[hide]
[]%=id {n} {x ∷ xs} {zero}  = refl
[]%=id {n} {x ∷ xs} {suc j} = cong (λ tail → x ∷ tail) []%=id
\end{code}
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
swapat (s , t) j = isoToEquiv (iso (permuteAt s t j) (permuteAt s t j) (permuteAtTwice s t j) (permuteAtTwice s t j))
\end{code}

For the \texttt{noop} law we need to show that \texttt{swapat} respects it.
We proceed in two steps. First \texttt{swassId} shows that the underlying function of the equivalence
\texttt{swapat (s , s) j} is the identity function. Then, since two equivalences are equal if their
underlying functions are equal we get an identification of \texttt{swapat (s , s) j} and the identity equivalence.
\begin{code}
permuteId : {s : String} → (t : String) → permute (s , s) t ≡ id t
permuteId {s} t with t =? s | t =? s
...               | yes t=s | yes _   = sym (ptoc t=s)
...               | yes _   | no _    = refl
...               | no t≠s  | yes t=s = ⊥-elim (t≠s t=s)
...               | no _    | no _  = refl

swapssId : {s : String} {j : Fin size} → equivFun (swapat (s , s) j) ≡ idfun (repoType)
swapssId {s} {j} = funExt pointwise
  where
    pointwise : (r : repoType) → equivFun (swapat (s , s) j) r ≡ idfun repoType r
    pointwise r = equivFun (swapat (s , s) j) r
                ≡⟨ cong (λ x → r [ j ]%= id x) (funExt permuteId) ⟩ r [ j ]%= id
                ≡⟨ []%=id ⟩ id r ∎

swapatIsId : {s : String} {j : Fin size} → swapat (s , s) j ≡ idEquiv repoType
swapatIsId = equivEq swapssId
\end{code}

With these pieces we are ready to interpret the repository HIT.
\texttt{I} sends \texttt{doc} to the type of string vectors, each patch to \texttt{ua} of the
\texttt{swapat} bijection and each \texttt{noop} square to \texttt{swapatIsId} composed with
\texttt{uaIdEquiv} which the path identifying \texttt{ua (idEquiv \_)} and \texttt{refl}.

Then we can interpret and apply patches like before.
\begin{code}
I : R → Type₀
I doc = repoType
I ((s1 ↔ s2 AT j) i) = ua (swapat (s1 , s2) j) i
I (noop s j i i') = (cong ua (swapatIsId {s} {j}) ∙ uaIdEquiv) i i'

interp : (doc ≡ doc) → repoType ≃ repoType
interp p = pathToEquiv (cong I p)

apply : (doc ≡ doc) → repoType → repoType
apply p = equivFun (interp p)
\end{code}

\subsection{A Patch Optimizer}
\begin{code}
noop-helper : {j : Fin size} {s1 s2 : String} → s1 ≡ s2
              → (s1 ↔ s2 AT j) ≡ refl
noop-helper {j} {s1} {s2} s1=s2 = cong (λ s → s ↔ s2 AT j) (s1=s2) ∙ noop s2 j

result-contractible : {X : Type} → (x : X) → isContr (Σ[ y ∈ X ] y ≡ x)
result-contractible x = (x , refl) , λ (y , p) → ΣPathP (sym p , λ i j → p (~ i ∨ j))

result-isSet : (x : R) → isSet (Σ[ y ∈ R ] y ≡ x)
result-isSet = isProp→isSet ∘ isContr→isProp ∘ result-contractible

opt : (x : R) → Σ[ y ∈ R ] y ≡ x
opt doc = (doc , refl)
opt x@((s1 ↔ s2 AT j) i) with s1 =? s2
...                       | yes s1=s2 = refl {x = doc} i , λ k → noop-helper {j} (ptoc s1=s2) (~ k) i
...                       | no _ = x , refl
opt (noop s j i k) = isOfHLevel→isOfHLevelDep 2 result-isSet
  (doc , refl) (doc , refl) (cong opt (s ↔ s AT j)) (cong opt refl) (noop s j) i k


optimize : (p : doc ≡ doc) → Σ[ q ∈ (doc ≡ doc) ] p ≡ q
optimize p = transport e (cong opt p)
  where
  e : (PathP (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl) (doc , refl))
      ≡ (Σ[ q ∈ doc ≡ doc ] p ≡ q)
  e = (PathP (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl) (doc , refl))
      ≡⟨ PathP≡Path (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl) (doc , refl) ⟩
        Path (Σ[ y ∈ R ] y ≡ doc) (transport (λ i → Σ[ y ∈ R ] y ≡ p i) (doc , refl)) (doc , refl)
      ≡⟨ cong (λ x → Path (Σ[ y ∈ R ] y ≡ doc) x (doc , refl)) (ΣPathP (refl , sym (lUnit p))) ⟩
        Path (Σ[ y ∈ R ] y ≡ doc) (doc , p) (doc , refl)
      ≡⟨ sym ΣPath≡PathΣ ⟩
        (Σ[ q ∈ doc ≡ doc ] (PathP (λ i → q i ≡ doc) p refl))
      ≡⟨ Σ-cong-snd (λ q → PathP≡Path (λ i → q i ≡ doc) p refl) ⟩
        (Σ[ q ∈ doc ≡ doc ] (transport (λ i → q i ≡ doc) p) ≡ refl)
      ≡⟨ Σ-cong-snd (λ q → cong (λ x → x ≡ refl) (path-transport-lemma q p)) ⟩
        (Σ[ q ∈ doc ≡ doc ] (sym q ∙ p) ≡ refl)
      ≡⟨ Σ-cong-snd (λ q → lemma q p) ⟩
        (Σ[ q ∈ doc ≡ doc ] p ≡ q) ∎
    where
    lemma : {X : Type} {x y : X} →
            (f g : x ≡ y) →
            (sym f ∙ g ≡ refl) ≡ (g ≡ f)
    lemma f g = sym f ∙ g ≡ refl
      ≡⟨ cong (λ x → (sym f ∙ g) ≡ x) (sym (lCancel f)) ⟩
        (sym f) ∙ g ≡ (sym f) ∙ f
      -- this is the key step: the rest is just groupoidLaw shuffling
      ≡⟨ ua (compl≡Equiv f (sym f ∙ g) (sym f ∙ f)) ⟩
        (f ∙ (sym f ∙ g)) ≡ f ∙ (sym f ∙ f)
      ≡⟨ cong₂ (λ a b → a ≡ b) (assoc f (sym f) g) (assoc f (sym f) f) ⟩
        (f ∙ sym f) ∙ g ≡ (f ∙ sym f) ∙ f
      ≡⟨ cong₂ (λ a b → (a ∙ g) ≡ b ∙ f) (rCancel f) (rCancel f) ⟩
        refl ∙ g ≡ refl ∙ f
      ≡⟨ cong₂ (λ a b → a ≡ b) (sym (lUnit g)) (sym (lUnit f)) ⟩
        g ≡ f ∎
\end{code}
