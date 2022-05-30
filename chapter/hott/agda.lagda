% run `agda --latex` on this file to generate the actual LaTeX in ./latex/
\section{Agda}
In this section we introduce Agda~\cite{Agda} -- a dependently typed programming language
and proof assistant.
The goal is to introduce enough of its syntax and workings to follow the formalization in \autoref{ch/formalization}.

The basic syntax of Agda will be familiar to users of Haskell~\cite{haskell2010},
but with \texttt{:} for typing and significant use of unicode (including $\rightarrow$
for function types). In general, terms will appear as \texttt{term : Type} followed by
\texttt{term = ...} where the first line provides the type and the second defines the
specific term.

As an example, we consider the type of vectors and operations on them.
This is a dependent type that provides a good look at the syntax and features of
Agda as a programming language.

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
Vectors also have two constructors. The empy vector \texttt{[~]} has length zero, and a vector of any length can be extended by adding a new element to the start.
The implicit argument \texttt{\{n~:~ℕ\}} should be read as "for all natural numbers n..." (and in fact we could write \texttt{∀~\{n\}} since Agda can easily infer that n must be a natural number).
\begin{code}
data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}

Note that the data declaration has \texttt{A} before the colon, but \texttt{ℕ} after.
This is because \texttt{A} stays constant over the two constructors, while the natural number varies.

The cons function (\texttt{\_::\_}) shows two important features of Agda's syntax: infix notation and currying.
Infix functions can be used between its arguments -- in this case \texttt{(x::xs)} is a vector --
and are denoted by underscores.
Each underscore in the name represents a position in which we may place the corresponding argument.

Currying means that a function like \texttt{\_::\_} that takes two arguments of types
\texttt{A} and \texttt{Vec A n} and produces a \texttt{Vec A (suc n)} can be written as
\texttt{\_::\_ : A → Vec A n → Vec A (suc n)} (with → associating to the right).
~\footnote{This is possible because of the product~$\dashv$~exponentiation
adjunction in cartesian closed categories which gives a bijection
between $(A \times B) \rightarrow C$ and $A \rightarrow (B \rightarrow C)$ for all objects A, B and C
See IV.6: Cartesian Closed Categories in~\cite{maclane1998}}.

This style allows for partial application of functions where \texttt{\_::\_ x} results
in a unary function \texttt{Vec A n → Vec A (suc n)}.
Mixfix operators and currying interact wonderfully with partial application. \texttt{x ::\_} is the
function that takes a vector and conses x onto it.

Now we can construct terms of this new type.
For example, here is the 3-vector of natural numbers [1,2,3]:
\begin{code}
one-two-three : Vec ℕ (suc (suc (suc zero)))
one-two-three = suc zero
  :: (suc (suc zero)
    :: (suc (suc (suc zero))
      :: []))
\end{code}
Clearly this way to write out natural numbers is pretty verbose.
Agda's builtin type of naturals lets us write \texttt{3} instead of \texttt{suc (suc (suc zero))}.

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
To make use of the additional power of dependent types we can define \texttt{map-pointwise}
which safely applies a different function to each element of a vector.
\begin{code}
map-pointwise : {A B : Set}{n : ℕ} →
                Vec (A → B) n → Vec A n → Vec B n
map-pointwise [] [] = []
map-pointwise (f :: fs) (x :: xs) = f x :: map-pointwise fs xs
\end{code}

Concatenation is the binary operation that adjoins one vector to the end of another.
This has the effect of adding their lengths, evidenced by the resulting type \texttt{Vec A (n + m)}.
Note that we only pattern match on the left vector. This is actually important, since \texttt{\_+\_} is defined
by pattern matching on its left argument, allowing this definition to type-check.
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
+-runit : ∀ {n} → n + zero ≡ n
+-runit {zero} = refl
+-runit {suc n} = cong suc +-runit
\end{code}
For \texttt{+-runit} we need a proof by induction. The base case (0 + 0 = 0) is proved by \texttt{refl}
like before, but the induction step requires slightly more work.
Luckily, the term we need has type \texttt{(suc n + zero) ≡ suc n} and the left-hand side computes to \texttt{suc (n + zero)}.
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
