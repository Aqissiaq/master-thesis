% run `agda --latex` on this file to generate the actual LaTeX in ./latex/
\section{Agda}
In this section we introduce Agda~\cite{Agda} -- a dependently typed programming language / proof assistant.
The goal is to introduce enough of its syntax and workings to follow the formalization in \autoref{ch/formalization}.

The basic syntax of Agda is similar to that of Haskell [CITATION?], but with \texttt{:} for typing and significant use of unicode (including $\rightarrow$ for function types).

As an example of Agda as a dependently typed programming language,
let us consider the type of vectors and operations on them.
This is a simple dependent type which will give us a good look at Agda's syntax and features.

First, we are going to need the natural numbers (recall that vectors are a family of types indexed by natural numbers).
The (Peano) natural numbers are an inductive type, which we introduce with the \texttt{data} keyword.
It has two constructors: \texttt{zero} and \texttt{suc}.
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
\end{code}
\begin{code}[hide]
_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

open import Relation.Binary.PropositionalEquality
\end{code}

We can now define vectors as a family of types indexed by a type and a natural number.
Vectors also have two constructors. The empy vector \texttt{[]} has length zero, and a vector of any length can be extended by adding a new element to the start.
The implicit argument \texttt{\{n~:~ℕ\}} should be read as "for all natural numbers n..." (and in fact we could write \texttt{∀~\{n\}} since Agda can easily infer that n must be a natural number).

The cons function (\texttt{\_::\_}) shows two important features of Agda's syntax: infix notation and currying.
Infix functions can be used between its arguments, in this case \texttt{x :: xs} would be a vector,
and are denoted by underscores. Each underscore in the name represents a position in which we may place
the corresponding argument.

Currying (Named after Haskell Curry [CITATION?]) is a way to describe functions with multiple arguments
by making use of the product~$\dashv$~exponentiation adjunction.
This adjunction gives a bijection between $(A \times B) \rightarrow C$ and $A \rightarrow (B \rightarrow C)$
for all objects A, B and C [I CANNOT DO THIS WITHOUT INTRODUCING MORE CATEORY THEORY. FOOTNOTE? Maclane IV.6: CCC's] which
means we can write the type of a function which takes multiple arguments as a sequence of types with right
arrows (associating to the right).

[FOOTNOTE?] mixfix operators and currying interact wonderfully with partial application. \texttt{x ::\_} is the
function that takes a vector and conses x onto it.
\begin{code}
data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}
Note that the first line has \texttt{A} before the colon, but \texttt{ℕ} after.
This is because \texttt{A} stays constant over the two constructors, while the natural number varies.

Now we can construct terms of this new type.
For example, here is the 3-vector of natural numbers [1,2,3]:
\begin{code}
one-two-three : Vec ℕ (suc (suc (suc zero)))
one-two-three = suc zero
  :: (suc (suc zero)
    :: (suc (suc (suc zero))
      :: []))
\end{code}

We can also define convenient functions on vectors, like \texttt{map} and concatenation.
Here \texttt{map} is defined by pattern matching on the vector. It applies a given function f to each element
of the vector, potentially changing its underlying type, but not its length.
The two types \texttt{A} and \texttt{B}, as well as the length of the vector, are left implicit and can
be inferred from the provided function and vector.
\begin{code}
map : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
map _ [] = []
map f (x :: v) = (f x) :: (map f v)
\end{code}

Of course, map would work equally well for the non-dependent type of lists.
To make use of this additional power we can define \texttt{map-pointwise}
which safely applies a different function to each element.
\begin{code}
map-pointwise : {A B : Set}{n : ℕ} →
                Vec (A → B) n → Vec A n → Vec B n
map-pointwise [] [] = []
map-pointwise (f :: fs) (x :: xs) = f x :: map-pointwise fs xs
\end{code}

Concatenation is the binary operation that adjoins one vector to the end of another.
This has the effect of adding their lengths, evidenced by the resulting type \texttt{Vec A (n + m)}.
Note that we only pattern match on the left vector. This is actually important, since \texttt{\_+\_} is defined
by pattern matching on its left argument, allowing this definition to type-check. [SHOW +?]
\begin{code}
_++_ : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
\end{code}

In addition to being a dependently typed functional programming language
(or perhaps more accurately, \emph{by} being a dependently typed programming language)
Agda is a proof assistant. By making use of "propositions as types" as well as Martin-Löf style
identity types, proofs and programs are the same thing.
Note that the Agda type \texttt{\_≡\_} is \emph{not} the same as the judgemental equality from \autoref{sec/typetheory}.
Rather, it is the identity type described in \autoref{sec/identitytypes}.

The most basic proofs are simply \texttt{refl}. We can use refl to prove that one plus one is two,
or that zero is the left unit of addition.
\begin{code}
-- 1 + 1 = 2
_ : (suc zero) + (suc zero) ≡ suc (suc zero)
_ = refl

-- zero is the left unit for addition
+-lunit : ∀ {n} → zero + n ≡ n
+-lunit = refl
\end{code}
Of course, not all proofs are so simple. In fact, proving that zero is also the \emph{right} unit takes some work.
This is because addition is defined by induction on the left argument, so \texttt{+-lunit} is simply the base case.

\begin{code}
-- zero is the right unit for addition
+-runit : ∀ {n} → n + zero ≡ n
+-runit {zero} = refl
+-runit {suc n} = cong suc +-runit
\end{code}
For \texttt{+-runit} we need a proof by induction. The base case (0 + 0 = 0) is proved by \texttt{refl}
like before, but the induction step requires slightly more work.
Luckily the term we need has type \texttt{(suc n + zero) ≡ suc n} and the left-hand side computes to \texttt{suc (n + zero)}.
Now we have \texttt{suc} applied to both sides of an instance of \texttt{+-runit} so we can use the induction hypothesis with \texttt{cong : (f : X → Y) → x ≡ y → (f x) ≡ (f y)}.
(Also note the pattern matching on an implicit argument.)

Another useful tool, mainly to make complicated proofs easier to follow, is \texttt{≡-Reasoning},
which introduces \texttt{\_≡⟨\_⟩\_} and \texttt{\_∎}.
These let the programmer write out the steps of a proof, like the inductive case of the proof below,
such that \texttt{x ≡⟨ p ⟩ y} means "x is equal to y by p".
\begin{code}
open ≡-Reasoning
concat-map : {A B : Set} {n m : ℕ} → (f : A → B) (v : Vec A n) (w : Vec A m)
             → map f (v ++ w) ≡ (map f v) ++ (map f w)
concat-map f [] w = refl
concat-map f (x :: v) w = map f ((x :: v) ++ w)
  ≡⟨ refl ⟩ map f (x :: (v ++ w))
  ≡⟨ refl ⟩ f x :: map f (v ++ w)
  ≡⟨ cong (f x ::_) (concat-map f v w) ⟩
    (map f (x :: v) ++ map f w) ∎
\end{code}
