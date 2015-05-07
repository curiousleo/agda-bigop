\nonstopmode
\documentclass[12pt,chapterprefix=true,toc=bibliography,numbers=noendperiod,
               footnotes=multiple,twoside]{scrreprt}

\newcommand{\AGDALATEX}[1]{#1}
\newcommand{\PLAINLATEX}[1]{}

\usepackage{amsmath}
\usepackage{polyglossia}
\setmainlanguage[variant=british]{english}
\usepackage{fontspec}
% \setmainfont{erewhon}
% \setsansfont{Gillius ADF}[Scale=MatchLowercase]
% \setmonofont{Source Code Pro}[Scale=MatchLowercase]
\usepackage[]{unicode-math}

\usepackage{microtype}
\usepackage{bussproofs}
\usepackage{csquotes}
\usepackage[autocite=footnote,citestyle=authoryear-comp,bibstyle=authoryear,
            dashed=false,isbn=false,doi=false,backend=biber]{biblatex}
\usepackage[bookmarks,hidelinks]{hyperref}
\usepackage[noabbrev,capitalise]{cleveref}

\AGDALATEX{%
\usepackage{agda}
}
\PLAINLATEX{%
\usepackage{verbatim}
\newenvironment{code}{\verbatim}{\endverbatim}
\long\def\AgdaHide#1{} % Used to hide code from LaTeX.
}
\usepackage{newunicodechar}
\newunicodechar{ℓ}{\ensuremath{ℓ}}
\newunicodechar{≈}{\ensuremath{≈}}
\newunicodechar{≋}{\ensuremath{≋}}
\newunicodechar{⊔}{\ensuremath{⊔}}
\newunicodechar{→}{\ensuremath{→}}
\newunicodechar{←}{\ensuremath{←}}
\newunicodechar{ℕ}{\ensuremath{ℕ}}
\newunicodechar{∀}{\ensuremath{∀}}
\newunicodechar{∃}{\ensuremath{∃}}
\newunicodechar{λ}{\ensuremath{λ}}
\newunicodechar{≡}{\ensuremath{≡}}
\newunicodechar{≢}{\ensuremath{≢}}
\newunicodechar{×}{\ensuremath{×}}
\newunicodechar{⊗}{\ensuremath{⊗}}
\newunicodechar{∣}{\ensuremath{∣}}
\newunicodechar{¬}{\ensuremath{¬}}
\newunicodechar{∘}{\ensuremath{∘}}
\newunicodechar{∙}{\ensuremath{∙}}
\newunicodechar{ε}{\ensuremath{ε}}
\newunicodechar{Σ}{\ensuremath{Σ}}
\newunicodechar{…}{\ensuremath{…}}
\newunicodechar{∥}{\ensuremath{∥}}
\newunicodechar{□}{\ensuremath{□}}
\newunicodechar{∎}{\ensuremath{∎}}
\newunicodechar{⟩}{\ensuremath{⟩}}
\newunicodechar{⟨}{\ensuremath{⟨}}
\newunicodechar{≣}{\ensuremath{≣}}
\newunicodechar{ˡ}{\ensuremath{^{l}}}
\newunicodechar{ʳ}{\ensuremath{^{r}}}
\newunicodechar{➀}{\ensuremath{➀}}
\newunicodechar{➁}{\ensuremath{➁}}

\hypersetup{
  pdftitle={Big Operators in Agda},
  pdfauthor={Leonhard Markert (lm510), Emmanuel College}
}
\addbibresource{Bibliography.bib}
\title{Big Operators in Agda}
\author{Leonhard Markert \\ Emmanuel College}

\setlength{\mathindent}{\parindent}
\setlength{\bibitemsep}{.5\baselineskip}
\setcounter{secnumdepth}{2}
\urlstyle{same} % normal text font (alternatives: tt, rm, sf)
\pagestyle{headings}
\addtokomafont{pagehead}{\itshape}

\begin{document}
\setmathfont{Asana-Math.otf}

\begin{titlepage}
\maketitle
\end{titlepage}

\tableofcontents

\AgdaHide{
\begin{code}
module Report where
\end{code}
%TC:endignore
}

\chapter{Introduction}

\section{Motivation}

\section{Agda basics}

\AgdaHide{
%TC:ignore
\begin{code}
module Basics where
  open import Level renaming (zero to lzero; suc to lsuc)

  -- infixr 5 _∷_
\end{code}
%TC:endignore
}

This project was implemented in \emph{Agda}, a functional programming language with a dependent type system. \emph{Functional programming} is a declarative paradigm where computation proceeds by evaluating expressions (instead of, say, changing the state of an abstract machine.) In a \emph{dependent} type system, types can contain (depend on) terms. We will discuss what this means in XXX.

In comparison to non-dependent functional languages like Haskell or ML, the type system is more expressive: it serves as a higher-order logic. The downside is that type inference is undecidable, so most terms need type annotations.

Here we introduce the syntax of the language. The following sections explains how Agda can be used to write theorems and check proofs.

\minisec{Simple types and functions}

Truth values (Booleans) can be defined in Agda as follows:

%TC:ignore
\begin{code}
  data Bool : Set where
    true   :  Bool
    false  :  Bool
\end{code}
%TC:endignore

We introduce a new type \AgdaDatatype{Bool} with two constructors, \AgdaInductiveConstructor{true} and \AgdaInductiveConstructor{false}. Both construct elements of \AgdaDatatype{Bool}, so that is the type we annotate them with (after the colon). It may come as a surprise that the type itself needs an annotation, too. In Agda, the type of simple types is called \AgdaPrimitiveType{Set}. Since \AgdaDatatype{Bool} is a simple type, we declare it to be of type \AgdaPrimitiveType{Set}. [XXX forward-reference to explanation of type hierarchy]

Let us now write a function using this newly introduced datatype. \AgdaFunction{not} flips the Boolean passed to it:

%TC:ignore
\begin{code}
  not : Bool → Bool
  not true   =  false
  not false  =  true
\end{code}
%TC:endignore

This function takes a \AgdaDatatype{Bool} and returns a \AgdaDatatype{Bool}, so the type of the function as a whole is \AgdaDatatype{Bool} \AgdaSymbol{→} \AgdaDatatype{Bool}. It is defined by pattern matching: the result of the function is the term on the right-hand side of the equality sign if its input matches the left-hand side.

Note that the pattern matching must cover all possible cases. More generally speaking, all Agda functions must be \emph{total}, that is, defined on all values of its argument types.

Agda identifiers can contain Unicode symbols, which makes it possible to use notation familiar from mathematics in Agda code. The function \AgdaFunction{\_∧\_} computes the logical conjunction of its inputs:

%TC:ignore
\begin{code}
  _∧_ : Bool → _ → Bool
  true  ∧ true  = true
  _     ∧ _     = false
\end{code}
%TC:endignore

An underscore (the symbol \enquote{\_}) can be interpreted in three different ways in Agda, depending on where it is used. This slightly contrived example covers them all:

\begin{description}
\item[In an identifier] like \AgdaFunction{\_∧\_}, the underscores indicate where the function or type expects its arguments. This allows programmers to introduce new infix and mixfix operators.\footnote{\textcite{danielsson_parsing_2011} presents a general framework for parsing mixfix operators, of which infix operators are a special case.}
\item[In place of a term or type] an underscore stands for a value that is to be inferred by Agda. In the type of our function, \AgdaDatatype{Bool} \AgdaSymbol{→} \AgdaSymbol{\_} \AgdaSymbol{→} \AgdaDatatype{Bool}, the underscore marks the type of the second argument to \AgdaFunction{\_∧\_}. It is easily resolved: in the first pattern, the second argument is matched with \AgdaInductiveConstructor{true}, which is a constructor for the type \AgdaDatatype{Bool}. The underscore must therefore stand for \AgdaDatatype{Bool}.
\item[As a pattern] the underscore matches anything. It acts like a fresh variable that cannot be referred to. The definition of \AgdaFunction{\_∧\_} can thus be read as \enquote{the conjunction of two Booleans is true if both arguments are true; in any other case, the result is false.}
\end{description}

Let us consider a type with more structure. A natural number is either zero, or the successor of some natural number. In Agda, this inductive definition is written as

%TC:ignore
\begin{code}
  data ℕ : Set where
    zero  : ℕ
    suc   : ℕ → ℕ
\end{code}
%TC:endignore

Addition of natural numbers can then be defined as follows:

%TC:ignore
\begin{code}
  _+_ : ℕ → ℕ → ℕ
  zero   + n = n
  suc m  + n = suc (m + n)
\end{code}
%TC:endignore

Note that Agda functions defined on inductive types must not only be total, but also \emph{terminating}.\footnote{Functions defined on \emph{coinductive} types, on the other hand, must be \emph{productive}. \textcite{altenkirch_termination_2010} discusses the issue of termination checking functions on nested inductive and coinductive types.} Since termination checking is undecidable in general, Agda checks whether the arguments to the recursive call are structurally smaller than the arguments to the caller as a safe syntactic approximation to termination. This is clearly the case in the recursive case of \AgdaFunction{\_+\_}: the arguments to the caller are \AgdaInductiveConstructor{suc} \AgdaBound{m} and \AgdaBound{n} whereas those passed used in the recursive call are \AgdaBound{m} and \AgdaBound{n}. Structurally, \AgdaBound{m} is smaller than \AgdaInductiveConstructor{suc} \AgdaBound{m} so Agda can infer that the function terminates on all inputs.\footnote{A formal definition of \emph{structurally smaller}, is given in \textcite{coquand_pattern_1992}.}

\minisec{The type hierarchy and universe polymorphism}

Both \AgdaDatatype{Bool} and \AgdaDatatype{ℕ} as well as all the functions we have seen so far could have been written in a very similar way in Haskell or ML, modulo syntax. We will now see how Agda is different from non-dependent functional languages.

Every type in Agda resides somewhere in a type universe with countably infinite levels. In other words, if a type \AgdaBound{A} is valid, then there exists some level \AgdaBound{a} such that \AgdaBound{A} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaBound{a}. The reason for introducing a hierarchy of types in the first place is that allowing a typing judgement like \AgdaPrimitiveType{Set} \AgdaSymbol{:} \AgdaPrimitiveType{Set} leads to an inconsistent logic, a phenomenon referred to as \emph{Girard's paradox} in the literature. (XXX reference! Stanford philo etc, System U?).

\AgdaDatatype{Bool} and \AgdaDatatype{ℕ} are examples of simple types, which is expressed in Agda as \AgdaDatatype{Bool} \AgdaDatatype{ℕ} \AgdaSymbol{:} \AgdaPrimitiveType{Set} (note that we can give type declarations for terms of the same type in one go in this way.) \AgdaPrimitiveType{Set} is a synonym for \AgdaPrimitiveType{Set} \AgdaNumber{0}, which is itself of type \AgdaPrimitiveType{Set} \AgdaNumber{1}.\footnote{We use numbers \AgdaNumber{0}, \AgdaNumber{1}, \AgdaNumber{2} to denote universe levels for brevity here. In actual code, elements of the opaque type \AgdaPrimitiveType{Level} can only be constructed using the postulated functions \AgdaFunction{lzero} and \AgdaFunction{lsuc}.} This gives rise to an infinite hierarchy of types:
\begin{align*}
\text{\AgdaDatatype{Bool} \AgdaDatatype{ℕ} \AgdaSymbol{…}}\;&\AgdaSymbol{:}\;\text{\AgdaPrimitiveType{Set} \AgdaNumber{0}} \\
\text{\AgdaPrimitiveType{Set} \AgdaNumber{0}}\;&\AgdaSymbol{:}\;\text{\AgdaPrimitiveType{Set} \AgdaNumber{1}} \\
\text{\AgdaPrimitiveType{Set} \AgdaNumber{1}}\;&\AgdaSymbol{:}\;\text{\AgdaPrimitiveType{Set} \AgdaNumber{2}} \\
\text{\AgdaPrimitiveType{Set} \AgdaBound{n}}\;&\AgdaSymbol{:}\;\text{\AgdaPrimitiveType{Set} \AgdaSymbol{(}\AgdaFunction{lsuc} \AgdaBound{n}\AgdaSymbol{)}} \\
\end{align*}

With the concept of universe levels in mind, we now look at how the Agda standard library defines the type of lists:

%TC:ignore
\begin{code}
  data List {a : Level} (A : Set a) : Set a where
    []   : List A
    _∷_  : A → List A → List A
\end{code}
%TC:endignore

Consider two examples first. The list \AgdaFunction{bools} contains Boolean values. Here the carrier type of the list, \AgdaBound{A}, is instantiated to \AgdaDatatype{Bool}.

%TC:ignore
\begin{code}
  bools : List Bool
  bools = true ∷ (false ∷ ((true ∧ false) ∷ []))
\end{code}
%TC:endignore

In the datatype declaration of \AgdaDatatype{List}, the names \AgdaBound{a} and \AgdaBound{A} are left of the colon. They are global to the constructors of the datatype and called \emph{parameters}. The parameter \AgdaBound{a} is written in curly braces, which marks it as an \emph{implicit} parameter. This means that Agda will try to infer its value if it is not given explicitly.

\AgdaDatatype{Bool} has type \AgdaPrimitiveType{Set} \AgdaNumber{0}, so Agda correctly infers that in the type of \AgdaFunction{bools}, \AgdaBound{a} must be \AgdaNumber{0}. If we wanted to be explicit, we could have written the declaration as \AgdaFunction{bools} \AgdaSymbol{:} \AgdaDatatype{List} \AgdaSymbol{\{}\AgdaNumber{0}\AgdaSymbol{\}} \AgdaDatatype{Bool} instead.

Why is the parameter \AgdaBound{a} necessary at all? Since our definition of \AgdaDatatype{List} abstracts over the level of its carrier type, we can also build lists the live higher up in the type hierarchy. We might for example want to create a list of types:

%TC:ignore
\begin{code}
  types : List Set
  types = Bool ∷ (((ℕ → ℕ) → Bool) ∷ [])
\end{code}
%TC:endignore

Here the carrier type of the list is instantiated as \AgdaPrimitiveType{Set}, which is itself of type \AgdaPrimitiveType{Set} \AgdaNumber{1}. The value of the implicit parameter \AgdaBound{a} is inferred as level \AgdaNumber{1}. Note that the function type \AgdaSymbol{(}\AgdaDatatype{ℕ} \AgdaSymbol{→} \AgdaDatatype{ℕ}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{Bool} is also a simple type.

Lists defined in this way are \emph{universe polymorphic}, meaning that the universe level at which any particular list resides depends on its parameters. Making a parameter or argument of type \AgdaPrimitiveType{Level} implicit is common practice in Agda. Most of the time, the type checker can infer universe levels without ambiguity.

\minisec{Dependent types}

We now turn to the classic example of a dependent datatype: fixed-length lists, or \emph{vectors}.

%TC:ignore
\begin{code}
  data Vec {a} (A : Set a) : ℕ → Set a where
    []   : Vec A zero
    _∷_  : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}
%TC:endignore

The parameters (on the left-hand side of the colon in the type declaration) are the same as for \AgdaDatatype{List}, a type level \AgdaBound{a} and a type \AgdaBound{A}. Note that we have not specified the type of \AgdaBound{a}---Agda infers that it must be a \AgdaPrimitiveType{Level}. In addition to the parameters, the type \AgdaDatatype{Vec} is \emph{indexed} by a natural number, hence the \AgdaDatatype{ℕ} on the right-hand side of the colon. While parameters are the same for all constructors, indices may differ: the constructor \AgdaInductiveConstructor{[]} returns a \AgdaInductiveConstructor{zero}-length vector, while \AgdaInductiveConstructor{\_∷\_} takes an element and a vector of length \AgdaBound{n} and returns a vector of length \AgdaInductiveConstructor{suc} \AgdaBound{n}.

The vector append function \AgdaFunction{\_++\_} demonstrates how dependent types can be used to write (partially) verified code. It takes two vectors of length \AgdaBound{m} and \AgdaBound{n}, respectively, and returns a vector of length \AgdaBound{m} \AgdaFunction{+} \AgdaBound{n}. The fact that the type checker accepts the definition of this function means that the length of the vector that is returned always is the sum of the lengths of the input vector. This gives us some reassurance that the function does something sensible.

%TC:ignore
\begin{code}
  _++_ :  {a : Level} {m : ℕ} {n : ℕ} → {A : Set a} →
          Vec A m → Vec A n → Vec A (m + n)
  []        ++ ys = ys
  (x ∷ xs)  ++ ys = x ∷ (xs ++ ys)
\end{code}
%TC:endignore

As another example, consider a function \AgdaFunction{head} which returns the first element of a vector. Applying it to an empty vector makes no sense, as there is no first element to return. We would therefore like to restrict the argument of the function to vectors containing at least one element. The type of the following function does just that:

%TC:ignore
\begin{code}
  head : ∀ {n a} {A : Set a} → Vec A (suc n) → A
  head (x ∷ _) = x
\end{code}
%TC:endignore

But what about totality? Earlier we said that the patterns of a function must cover all possible arguments of its type. If we look close enough, we can see that this principle is not violated here even though there is no pattern for the empty vector. The reason is that the constructor for the empty vector has type \AgdaInductiveConstructor{[]} \AgdaSymbol{:} \AgdaDatatype{Vec} \AgdaBound{A} \AgdaInductiveConstructor{zero}. Agda knows that \AgdaInductiveConstructor{suc} \AgdaBound{n} and \AgdaInductiveConstructor{zero} cannot be unified, so we do not have to (and indeed cannot) supply a pattern for the empty list, which is exactly what wanted. This is a first example of the powerful interplay between dependent types and pattern matching.
%Later we will see dotted patterns, absurd patterns and the \AgdaKeyword{with} construct.

Lastly, we consider the type of finite sets \AgdaDatatype{Fin}, indexed by a natural number:\footnote{In the Agda standard library, the constructors for both \AgdaDatatype{ℕ} and \AgdaDatatype{Fin} are called \AgdaInductiveConstructor{zero} and \AgdaInductiveConstructor{suc}. Overloaded identifiers are allowed. If a name has multiple definitions and it is not clear from the context which one is being referred to, it must be qualified. Instead of \AgdaInductiveConstructor{zero} we may write \AgdaInductiveConstructor{ℕ.zero} or \AgdaInductiveConstructor{Fin.zero}, for example.}

%TC:ignore
\begin{code}
  data Fin : ℕ → Set where
    fzero  : {n : ℕ} → Fin (suc n)
    fsuc   : {n : ℕ} → Fin n → Fin (suc n)
\end{code}
%TC:endignore

One way to think about this type is that its value represents a natural number with its index as an upper bound. The type \AgdaDatatype{Fin}~\AgdaBound{n} has exactly \AgdaBound{n} different values, representing the numbers up to \(n-1\). \AgdaDatatype{Fin} \AgdaInductiveConstructor{zero} is empty; there is no way to construct a value of this type.

A bounded natural numbers can be used as an index into a vector. This lets us leverage the type system to eliminate out-of-bounds handling. Consider the (slightly contrived definition of a) function \AgdaFunction{lookup}, which takes a position bounded by \AgdaBound{n} and a vector of length \AgdaBound{n} and returns the element at this position:

%TC:ignore
\begin{code}
  lookup : ∀ {n a} {A : Set a} → Fin n → Vec A n → A
  lookup {.zero}  ()        []
  lookup          fzero     (x ∷ xs) = x
  lookup          (fsuc n)  (x ∷ xs) = lookup n xs
\end{code}
%TC:endignore

What is going on in the first pattern? Firstly, it shows that we can match against implicit arguments by position. Here we use the pattern \AgdaSymbol{\{}.\AgdaInductiveConstructor{zero}\AgdaSymbol{\}} to match the argument \AgdaBound{n}. The curly braces indicate that we are matching against an implicit argument. The dot before the pattern marks this pattern as the unique value of the correct type. It is unique in this case because the constructor of the empty vector \AgdaInductiveConstructor{[]} \AgdaSymbol{:} \AgdaDatatype{Vec} \AgdaBound{A} \AgdaInductiveConstructor{zero} appears in the same pattern, which forces the unification of \AgdaBound{n} with \AgdaInductiveConstructor{zero}. Note that \emph{dotted patterns} do not have to be implicit, and that implicit arguments can also be matched against by name. 

Secondly, since \AgdaBound{n} is unified with \AgdaInductiveConstructor{zero}, the position (the first non-implicit argument) would have to be of type \AgdaDatatype{Fin} \AgdaInductiveConstructor{zero}. But there is no value of this type! Agda's type checker can infer this and allows us to match this impossible value with \AgdaBound{()}, the \emph{absurd pattern}. No right-hand side is given for absurd patterns because they are never matched.

Note that in this particular example, it is not necessary to write down the first pattern. As with the function \AgdaFunction{head}, Agda can infer that the second and third pattern cover all possible inputs. However, in more complicated pattern matches, the absurd pattern is sometimes needed. It allows us to tell the totality checker explicitly which argument it is that cannot possibly be given.


\minisec{Record types}

The \AgdaKeyword{record} keyword lets us bundle terms and types together in a convenient manner. The type of a record field can depend on the values of any other field preceding it in the definition. A dependent pair type can be defined like this:

%TC:ignore
\begin{code}
  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      fst  : A
      snd  : B fst
\end{code}
%TC:endignore

The level of a record is the least upper bound of it fields' levels. In this case, it is the upper bound of \AgdaBound{a} and \AgdaBound{b} (written as \AgdaBound{a} \AgdaFunction{⊔} \AgdaBound{b}) to accomodate fields \AgdaField{fst} at levels \AgdaBound{a} and \AgdaField{snd} at level \AgdaBound{b}. Giving a \AgdaKeyword{constructor} is optional in general but required for pattern matching. It also makes defining new values less verbose---compare \AgdaFunction{pair₀} and \AgdaFunction{pair₁} in the next example.

In the type declaration of \AgdaDatatype{Σ}, the name \AgdaBound{B} is given to a function which takes a \emph{value} of type \AgdaBound{A} and returns a \emph{type} at level \AgdaBound{b}. The type of \AgdaField{snd} is defined as \AgdaBound{B} \AgdaBound{fst}, so it \emph{depends} on the value of \AgdaField{fst}. That is why \AgdaDatatype{Σ} is called a dependent pair. This type will become important in the next sections when predicates and existential quantifiers are discussed.

For now we will restrict ourselves to building non-dependent pairs, which means that we will systematically ignore the \AgdaBound{A}-typed parameter to \AgdaBound{B}. We can use \AgdaDatatype{Σ} to define non-dependent pairs like this:

%TC:ignore
\begin{code}
  _×_ : ∀ {a b} → Set a → Set b → Set _
  A × B = Σ A (λ _ → B)
\end{code}
%TC:endignore

This definition allows us to type non-dependent pairs more naturally:

%TC:ignore
\begin{code}
  pair₀ pair₁ : ℕ × Bool -- instead of Σ ℕ (λ _ → Bool)
  pair₁ = record { fst = zero ; snd = false }
  pair₀ = zero , false
\end{code}
%TC:endignore

As a \AgdaKeyword{record} type, \AgdaDatatype{Σ} can be deconstructed in many ways. The name of the type and the name of the field, separated by a dot, can be used to access that field (see \AgdaFunction{fst₀}). Alternatively, \AgdaKeyword{open} followed by the name of the type can be used to bring the names of the field accessors into scope (see \AgdaFunction{fst₁}). The fields themselves can be brought into scope by \AgdaKeyword{open}ing the type followed by the value whose fields we want to access (see \AgdaFunction{fst₂}). Note that \enquote{\AgdaKeyword{let} … \AgdaKeyword{in} \AgdaBound{x}} and \enquote{\AgdaBound{x}~\AgdaKeyword{where} …} can be used almost interchangeably. In the last example, we pattern match on the constructor of the type to extract its fields (see \AgdaFunction{fst₃}).

%TC:ignore
\begin{code}
  fst₀ fst₁ fst₂ fst₃ : ∀ {a b} {A : Set a} {B : Set b} → A × B → A
  fst₀ = Σ.fst
  fst₁ = let open Σ in fst
  fst₂ p = fst where open Σ p
  fst₃ (x , _) = x
\end{code}
%TC:endignore

\section{Relations, predicates and decidability}

%TC:ignore
\AgdaHide{
\begin{code}
module Relations where
  open import Data.Nat.Base
  -- open import Relation.Binary.PropositionalEquality

  infix 4 _≡_
\end{code}
}

\minisec{Relations}

Usually in mathematics, a relation between two sets is defined as a subset of the Cartesian product of the two sets. In a dependent type theory, a binary relation between types \AgdaDatatype{A} \AgdaSymbol{:} \AgdaPrimitiveType{Set} and \AgdaDatatype{B} \AgdaSymbol{:} \AgdaPrimitiveType{Set} has the type \AgdaDatatype{A} \AgdaSymbol{→} \AgdaDatatype{B} \AgdaSymbol{→} \AgdaPrimitiveType{Set}. Via currying, this type is isomorphic to \AgdaDatatype{A} \AgdaDatatype{×} \AgdaDatatype{B} \AgdaSymbol{→} \AgdaPrimitiveType{Set}. A common way to think about this constructive way of defining relations is to view the resulting type as evidence that the two arguments are related.

We will restrict our attention to the special case of relations between inhabitants of the same type, called \emph{homogeneous} relations.

One important homogeneous binary relation is called \emph{propositional equality}, written as \AgdaDatatype{\_≡\_} in Agda (also called \(I\) in the literature). Two elements of the same type are propositionally equal if they can be shown to reduce to the same value.

%TC:ignore
\begin{code}
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x
\end{code}
%TC:endignore

The relation \AgdaDatatype{\_≡\_} has only one constructor called \AgdaInductiveConstructor{refl}. In order to create an inhabitant of the propositional equality type, we must use this constructor---there is no other way.

The constructor \AgdaInductiveConstructor{refl} requires that its two arguments have the same value. Therefore, in order to obtain an inhabitant of \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{y}, \AgdaBound{x} and \AgdaBound{y} must be shown to reduce to the same value.

XXX: explain this

%TC:ignore
\begin{code}
  cong :  ∀ {a b} {A : Set a} {B : Set b}
          (f : A → B) {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl
\end{code}
%TC:endignore

As another example, \emph{Divisibility} is a familiar relation with a straightforward definition in Agda. It translates to \enquote{\(m\) divides \(n\) if there exists a \(q\) such that \(n \equiv q m\)}.

\begin{code}
  data _∣_ : ℕ → ℕ → Set where
    divides : {m n : ℕ} (q : ℕ) (eq : n ≡ q * m) → m ∣ n
\end{code}
%TC:endignore

XXX explain this

%TC:ignore
\begin{code}
  1-divides-n : ∀ n → 1 ∣ n
  1-divides-n n = divides {1} {n} n n≡n*1
    where
      n≡n*1 : ∀ {n} → n ≡ n * 1
      n≡n*1 {zero}  = refl
      n≡n*1 {suc n} = cong suc n≡n*1
\end{code}
%TC:endignore


\minisec{Predicates}

A predicate expresses some property of a term. In constructive logic, we often think of the values of a predicate as the \emph{evidence} that it holds. The type of a predicate over a type \AgdaDatatype{A} is \AgdaDatatype{A} \AgdaSymbol{→} \AgdaPrimitiveType{Set}.

We will consider two predicates over natural numbers as examples in this chapter, \AgdaDatatype{Even} \AgdaSymbol{:} \AgdaDatatype{ℕ} \AgdaSymbol{→} \AgdaPrimitiveType{Set} and \AgdaDatatype{Collatz} \AgdaSymbol{:} \AgdaDatatype{ℕ} \AgdaSymbol{→} \AgdaPrimitiveType{Set}. In words, they mean the following:
\begin{itemize}
\item \AgdaDatatype{Even} \AgdaBound{n} provides evidence that \AgdaBound{n} is an even number. One way of defining this predicate is by stating that any even number is either equal to zero, or it is the successor of the successor of an even number.
\item \AgdaDatatype{Collatz} \AgdaBound{n} provides evidence that if we keep iterating the function \AgdaFunction{f} (defined below), starting with \AgdaFunction{f} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{n}\AgdaSymbol{)}, eventually the result will be the number \AgdaPrimitive{1}.
\[ f(n) =
	\begin{cases}
		n/2    & \text{if } n \equiv 0 \text{ (mod \(2\))} \\
		3n + 1 & \text{if } n \equiv 1 \text{ (mod \(2\))}
	\end{cases}
\]
We can provide evidence for this property by giving a natural number \AgdaBound{i} together with a proof that \AgdaFunction{iter} \AgdaFunction{f} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{n}\AgdaSymbol{)} \AgdaBound{i} \AgdaDatatype{≡} \AgdaPrimitive{1}.
\end{itemize}

%TC:ignore
\AgdaHide{
\begin{code}
module Predicates where
  open import Data.Fin
  open import Data.Nat
  open import Data.Nat.DivMod
  open import Data.Product using (∃)
  open import Relation.Nullary
  open import Relation.Unary using (Pred; Decidable)
  open import Relation.Binary.PropositionalEquality using (_≡_)
\end{code}
}

\begin{code}
  data Even : ℕ → Set where
    zero-even : Even zero
    ss-even   : {n : ℕ} → Even n → Even (suc (suc n))
\end{code}

XXX need to explain \AgdaKeyword{with} and absurd patterns first

\begin{code}
  Collatz : ℕ → Set
  Collatz n = ∃ λ m → iter f (suc n) m ≡ 1
    where
      f : ℕ → ℕ
      f n with n mod 2
      f n | zero     = n div 2
      f n | suc zero = suc (3 * n)
      f n | suc (suc ())

      iter : ∀ {A} → (A → A) → A → ℕ → A
      iter f x zero    = x
      iter f x (suc n) = iter f (f x) n
\end{code}
%TC:endignore

\minisec{Decidability}

The notion of relation and predicate as introduced above is very general. One question we may ask is whether there exists a terminating decision procedure for a given relation or predicate. In the case of a predicate \AgdaDatatype{P} \AgdaSymbol{:} \AgdaDatatype{A} \AgdaSymbol{→} \AgdaPrimitiveType{Set}, a decision procedure would be a function which for any argument \AgdaBound{x} \AgdaSymbol{:} \AgdaDatatype{A} returns either an inhabitant of type \AgdaDatatype{P} \AgdaBound{x} (evidence that the predicate holds) or an inhabitant of type \AgdaDatatype{¬} \AgdaDatatype{P} \AgdaBound{x} (evidence that the predicate does not hold).

Considering the two example again, a decision procedure for \AgdaDatatype{Even} is not entirely trivial, but still straightforward to define. The predicate \AgdaDatatype{Collatz}, on the other hand, has been shown by Conway (XXX reference) to be undecidable---this is an instance of a predicate for which no decision procedure exists.


\section{Truth, falsity, absurdity and type inhabitation}

XXX

\AgdaHide{
\begin{code}
module Truth where
  open import Level
\end{code}
}

%TC:ignore
\begin{code}
  record ⊤ : Set where
    constructor tt

  record ⊥ : Set where

  ¬_ : ∀ {p} → Set p → Set p
  ¬ P = P → ⊥
\end{code}
%TC:endignore

\section{Equivalences and setoids}

The main use case of the \AgdaModule{Bigop} library is to prove equalities. As an example, the Binomial Theorem can be stated as (Concrete Mathematics reference XXX) \[ (1 + x)^n = \sum_{k = 0}^n \binom{n}{k} \; x^k \]

The intended meaning of this equation seems clear---in English, the statement could be expressed as as follows: \begin{quote}For all numbers \(x\) and \(n\), let \(k\) range over all numbers from \(0\) to \(n\) and evaluate \(\binom{n}{k} \; x^k\) at each step. The sum of all those numbers is equal to the number obtained by evaluating \((1 + x)^n\).\end{quote}

Unfortunately, this description is too imprecise to be translated into a statement of formal mathematics. The first question we would have to answer is what \emph{kinds} of numbers \(x\) and \(n\) are. The notation suggests that \(n\) is an integer. It does not tell us whether the equation is supposed to hold if \(n\) is negative. The number \(x\) is less constrained by notation as exponentiation is defined even for complex and irrational numbers. Is the equation meant to cover them too?

Next, we have to define the meaning of each symbol that occurs in the formula. The definition of summation, exponentiation and binomial coefficients can be found in any mathematics textbook. The \enquote{big sum} symbol has two different obvious definitions (see XXX), but in this case they both turn out to evaluate to the same result.

The last thing we need to consider is the meaning of the equality sign. In dependent types based logics, this is where equivalences and setoids come in.

\minisec{Equivalences}

Equivalences capture the essence of what it means for two things to be equal. A relation \AgdaDatatype{\_≈\_} is an equivalence if it is \emph{reflexive} (\(\forall a.\ a \approx a\)), \emph{symmetric} (\(\forall a,b.\ a \approx b \rightarrow b \approx a\)) and \emph{transitive} (\(\forall a,b,c.\ a \approx b \wedge b \approx c \rightarrow a \approx c\)).

It is easy to see that the notion of equality we used in the example at the beginning of this section is an equivalence. Informally, it can be stated as \enquote{two terms are equivalent if they evaluate to the same number}. This intuition is captured by an equivalence called \emph{propositional equality}, written as \AgdaDatatype{\_≡\_} in Agda (also called \(I\) in the literature). Two elements of the same type are propositionally equal if they can be shown to reduce to the same expression.

\minisec{Setoids}

A \emph{setoid} packages a type, called the \emph{carrier}, with an equivalence relation defined on that type. In the Agda standard library, the equivalence is split up into its underlying relation and a proof that this relation is an equivalence.

%TC:ignore
\AgdaHide{
\begin{code}
module Setoids where
  open import Level
  open import Relation.Binary.Core
\end{code}
}

\begin{code}
  record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
    infix 4 _≈_
    field
      Carrier       : Set c
      _≈_           : Rel Carrier ℓ
      isEquivalence : IsEquivalence _≈_
\end{code}
%TC:endignore

% Σ[ k ← 0 … n $ n choose k * x ^ k ] ≈ (suc x) ^ n

\section{Algebra}

XXX need to explain why I'm using lists

XXX also: can define fold for semigroups on non-empty lists (BooleanAlgebra \ldots)

% The treatment of algebraic structures is one aspect in which the library presented here is very different from Coq's bigop module.

\minisec{Folds and monoids}

Fundamentally, given any binary operator \(\_\!\!\odot\!\!\_\), what is the meaning of \(\bigodot_{i \leftarrow \textit{Idx}} f(i)\)? There are two main issues here: (1) the index list \(I\) may be empty; (2) in order to compute the result, we need to decide in which order the operator is applied.

Before describing my solutions to these issues, let us first be a little more precise about the types involved. \(\textit{Idx}\) is a list whose elements are of type \(I\). The function \(f : I \rightarrow R\) takes those elements to a \emph{result} type \(R\). The binary operator is defined over this result type, so \(\_\!\!\odot\!\!\_ : R \rightarrow R \rightarrow R\). The entire big operator expression itself also has type \(R\).

This partly dictates the solution to issue (1): since the big operator expression has type \(R\), we must pick some \(\epsilon : R\) to which it evaluates if \(\textit{Idx}\) is empty, such that \(\bigodot_{i \leftarrow []} f(i) \equiv \epsilon\). What would be a sensible choice of \(\epsilon\)? Consider

\[
	\left(\bigodot_{i \leftarrow []} f(i) \right) \odot \left(\bigodot_{i \leftarrow \textit{Idx}} g(i)\right)
	\qquad \text{and} \qquad
	\left(\bigodot_{i \leftarrow \textit{Idx}} g(i)\right) \odot \left(\bigodot_{i \leftarrow []} f(i)\right)
\]

In both cases, it would be reasonable to expect the result to be equal to just \(\bigodot_{i \leftarrow \textit{Idx}} g(i)\). This requirement exactly amounts to saying that \(\epsilon\) should be the \emph{identity} for \(\_\!\!\odot\!\!\_\), that is, \(\epsilon \odot x \equiv x \odot \epsilon \equiv x\) for any \(x : R\).

Problem (2) is a little more subtle. Our goal is to define the meaning of a big operator by a series of applications of its underlying binary operator. This operation, common in in functional programming, is usually called \emph{fold}. Unfortunately, there are two natural ways to fold over lists: left-fold and right-fold.

\begin{align*}
	\textit{foldl} &\qquad \bigodot_{i \leftarrow \textit{Idx}} g(i) \equiv g(i_0) \odot (g(i_1) \odot (g(i_2) \odot \ldots )) \\
	\textit{foldr} &\qquad \bigodot_{i \leftarrow \textit{Idx}} g(i) \equiv ( \ldots ((g(i_0) \odot g(i_1)) \odot g(i_2)) \ldots )
\end{align*}

It is clearly not desirable to have any ambiguity over what the big operator expression evaluates to. The solution adopted by the library presented here is to force the left-fold and the right-fold to be equivalent by requiring the underlying operator to be \emph{associative}. Then \(r \odot (r' \odot r'') \equiv (r \odot r') \odot r''\) for any \(r, r', r'' : R\), making the fold unique.

Together, the solutions to the issues of empty lists and ambiguous folds mean that in order to create a well-defined big operator, the underlying binary operation must be associative and have an identity. In other words, we need a \emph{monoid}.

\minisec{Algebraic hierarchy in Agda}

The Agda standard library contains a hierarchy of algebraic structures. Because of its intended use in formalising algebraic path problems, the focus of this project was on semirings.

The following tables list the algebraic structures and their properties as defined in the Agda standard library's \AgdaModule{Algebra} module.

XXX: insert table

commutative monoids:


+ congruence lemmas.

semirings without one:

\begin{align*}
\sum_{i \leftarrow \textit{Idx}} \left(x \times f(i)\right)
&\equiv
x \times \left(\sum_{i \leftarrow \textit{Idx}} f(i)\right) \\
\sum_{i \leftarrow \textit{Idx}} \left(f(i) \times x\right)
&\equiv
\left(\sum_{i \leftarrow \textit{Idx}} f(i)\right) \times x \\
\end{align*}


\chapter{Implementation}

\section{Design}

\section{Fold}

In section XXX, it was argued that the meaning of any big operator can be expressed as a fold over a monoid. More precisely, we take in a list of elements in some index set, evaluate an expression on every member, and combine the results using the binary operator of the monoid. If the list is empty, the fold evaluates to the monoid's unit element.

One way of expressing this as a computation in a functional programming language is using the functions \AgdaFunction{map} and \AgdaFunction{crush} (reference!). \AgdaFunction{map} takes a function and a list and applies the function to each element of the list. \AgdaFunction{crush} reduces a list using a binary operator.

%TC:ignore
\AgdaHide{
\begin{code}
open import Algebra

module Folds {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where

  open import Data.List using (List; foldr; map)
  open import Function using (_∘_)

  open Monoid M renaming (Carrier to R)
\end{code}
}

\begin{code}
  fold : (I → R) → List I → R
  fold f = crush ∘ map f
    where
      crush : List R → R
      crush = foldr _∙_ ε
\end{code}
%TC:endignore

\begin{align*}
\text{\AgdaFunction{fold} \AgdaFunction{f} \AgdaSymbol{(}\AgdaBound{l₀} \AgdaInductiveConstructor{∷} \AgdaBound{l₁} \AgdaInductiveConstructor{∷} \AgdaBound{l₂} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}\AgdaSymbol{)}}
\quad&\equiv\quad \text{\AgdaSymbol{(}\AgdaFunction{crush} \AgdaFunction{∘} \AgdaFunction{map} \AgdaFunction{f}\AgdaSymbol{)} \AgdaSymbol{(}\AgdaBound{l₀} \AgdaInductiveConstructor{∷} \AgdaBound{l₁} \AgdaInductiveConstructor{∷} \AgdaBound{l₂} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}\AgdaSymbol{)}} \\
\quad&\equiv\quad \text{\AgdaFunction{crush} \AgdaSymbol{(}\AgdaFunction{map} \AgdaFunction{f} \AgdaSymbol{(}\AgdaBound{l₀} \AgdaInductiveConstructor{∷} \AgdaBound{l₁} \AgdaInductiveConstructor{∷} \AgdaBound{l₂} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}\AgdaSymbol{)}\AgdaSymbol{)}} \\
\quad&\equiv\quad \text{\AgdaFunction{crush} \AgdaSymbol{(}\AgdaFunction{f} \AgdaBound{l₀} \AgdaInductiveConstructor{∷} \AgdaFunction{f} \AgdaBound{l₁} \AgdaInductiveConstructor{∷} \AgdaFunction{f} \AgdaBound{l₂} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}\AgdaSymbol{)}\AgdaSymbol{)}} \\
\quad&\equiv\quad \text{\AgdaFunction{f} \AgdaBound{l₀} \AgdaFunction{∙} \AgdaSymbol{(}\AgdaFunction{f} \AgdaBound{l₁} \AgdaFunction{∙} \AgdaSymbol{(}\AgdaFunction{f} \AgdaBound{l₂}\AgdaSymbol{)}} \\
\quad&\equiv\quad \text{\AgdaFunction{f} \AgdaBound{l₀} \AgdaFunction{∙} \AgdaFunction{f} \AgdaBound{l₁} \AgdaFunction{∙} \AgdaFunction{f} \AgdaBound{l₂}}
\end{align*}

\begin{align*}
\text{\AgdaFunction{fold} \AgdaFunction{f} \AgdaInductiveConstructor{[]}}
\quad&\equiv\quad \text{\AgdaSymbol{(}\AgdaFunction{crush} \AgdaFunction{∘} \AgdaFunction{map} \AgdaFunction{f}\AgdaSymbol{)} \AgdaInductiveConstructor{[]}} \\
\quad&\equiv\quad \text{\AgdaFunction{crush} \AgdaSymbol{(}\AgdaFunction{map} \AgdaFunction{f} \AgdaInductiveConstructor{[]}\AgdaSymbol{)}} \\
\quad&\equiv\quad \text{\AgdaFunction{crush} \AgdaInductiveConstructor{[]}} \\
\quad&\equiv\quad \text{\AgdaBound{ε}}
\end{align*}

Since this library was created with matrix algebra in mind, the most important index type is (bounded) natural numbers, and the most important lists contain consecutive natural numbers.


\section{Filters}

Consider the following formula: \[ \sum_{\substack{0 \leq i < 2n+1 \\ (i\ \text{odd})}} i \equiv n^2 \]

An annotation is added here that we have not come across before: the condition (\(i\) odd). What this is saying is that when evaluating the formula, out of the natural numbers from zero to \(2n\), we only consider the ones which are odd, and throw away all the others.

In terms of types, \emph{odd} can be expressed as a decidable predicate. (Other option: function A -> Bool -- explain why decidable predicates are better XXX). \emph{Filtering} is the process of removing the elements that do not satisfy the predicate from the list.

In the spirit of modularity, filters were implemented as a function taking a list and a decidable predicate without any dependency on other parts of the library. The expression that generates the list of values for the example above is

% \begin{verbatim}
% 0 …+ suc (n + n) ∥ odd
% \end{verbatim}

where
% \begin{itemize}
% \item \texttt{0 …+ suc (n + n) : List ℕ},
% \item \texttt{odd : Decidable Odd} and
% \item \texttt{_∥_ : List I → Decidable P → List I}.
% \end{itemize}

% \begin{verbatim}
% ∀ n → Σ[ i ← 0 …+ suc (n + n) ∥ odd ] i ≈ n * n
% \end{verbatim}

\section{Monoid lemmas}

Monoids are endowed with an identity and an associativity law. Based on these two properties, there are a few things we can say about what happens when the monoid's binary operator is lifted into a big operator.

\minisec{Lifted identity}

The identity law can be lifted to give the following equivalence for the monoid's big operator:

% \[\bigodot_{i ← \textit{Idx}}ε &≡ ε\]

\[
\text{\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{is} \AgdaFunction{]} \AgdaFunction{ε} \AgdaDatatype{≈} \AgdaFunction{ε}}
\]

\minisec{Distributivity over \AgdaFunction{\_++\_}}

It follows from the monoid associativity law that the big operator distributes over the list append function \AgdaFunction{\_++\_} as follows:

\[\text{
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{++} \AgdaBound{ys} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i} \AgdaFunction{+} \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{ys} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i}
}\]

\minisec{Congruence}

\section{Commutative monoid lemmas}

\begin{align*}
\bigodot_{i ← \textit{Idx}} \left(f(i) \odot g(i)\right)
&≡
\left(\bigodot_{i ← \textit{Idx}} f(i) \right) \odot \left(\bigodot_{i ← \textit{Idx}} g(i)\right) && \text{merge} \\
\bigodot_{i ← \textit{Idx}_0} \left(\bigodot_{j ← \textit{Idx}_1} f(i,j)\right)
&≡
\bigodot_{j ← \textit{Idx}_1} \left(\bigodot_{i ← \textit{Idx}_0} f(i,j)\right) && \text{swap} \\
\bigodot_{i ← \textit{Idx}} f(i)
&≡
\left( \bigodot_{\substack{i ← \textit{Idx} \\ p\ i}} f(i) \right) ⊙ \left( \bigodot_{\substack{i ← \textit{Idx} \\ ¬ p\ i}} f(i) \right) && \text{split-P}
\end{align*}

\section{\enquote{Semiring without one} lemmas}

\section{Ordinals}

\section{\label{Impl-Matrices}Matrices}

In order to prove that square matrices over semirings are again semirings, it was necessary to formalise matrices first. This module is independent from the rest of the project.

%TC:ignore
\AgdaHide{
\begin{code}
module ReportMatrix where

  open import Data.Fin using (Fin)
  open import Data.Nat.Base using (ℕ)
  import Data.Vec as V
  open V using (Vec)
  import Data.Vec.Properties as VP
  open import Function using (_∘_)
  open import Function.Equivalence as Equiv using (_⇔_)
  open import Relation.Binary
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)
  open P.≡-Reasoning
  import Relation.Binary.Vec.Pointwise as VP
\end{code}
}
%TC:endignore

A matrix is defined as a vector of row vectors over some carrier type. \AgdaFunction{Matrix} \AgdaBound{A} \AgdaBound{r} \AgdaBound{c} is the type of \(r × c\) matrices over carrier \AgdaBound{A}.

%TC:ignore
\begin{code}
  Matrix : ∀ {a} (A : Set a) → ℕ → ℕ → Set a
  Matrix A r c = Vec (Vec A c) r
\end{code}
%TC:endignore

\AgdaFunction{lookup} \AgdaBound{i} \AgdaBound{j} \AgdaBound{m} returns the \(j\)th element of row \(i\) of the matrix \AgdaBound{m}, as expected. The second function allows us to write \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{j} \AgdaFunction{]} instead.

%TC:ignore
\begin{code}
  lookup : ∀ {r c a} {A : Set a} → Fin r → Fin c → Matrix A r c → A
  lookup i j m = V.lookup j (V.lookup i m)

  _[_,_] : ∀ {r c a} {A : Set a} → Matrix A r c → Fin r → Fin c → A
  m [ i , j ] = lookup i j m
\end{code}
%TC:endignore

\AgdaFunction{tabulate} populates a matrix using a function that takes the row and column index to an element of the matrix by applying that function to each position in the matrix. As an example, the transposition function is included too. Note how the change in the shape of the matrix is reflected in the return type of the function, where the number of rows and columns are swapped.

%TC:ignore
\begin{code}
  tabulate : ∀ {r c a} {A : Set a} → (Fin r → Fin c → A) → Matrix A r c
  tabulate f = V.tabulate (λ r → V.tabulate (λ c → f r c))

  transpose : ∀ {r c a} {A : Set a} → Matrix A r c → Matrix A c r
  transpose m = tabulate (λ c r → lookup r c m)
\end{code}
%TC:endignore

Lastly, the lemma \AgdaFunction{lookup∘tabulate} shows that if a matrix was created by tabulating a function \AgdaBound{f}, then looking up the element at row \AgdaBound{i} and column \AgdaBound{j} returns \AgdaBound{f} \AgdaBound{i} \AgdaBound{j}. The proof uses a similar lemma for vectors, \AgdaFunction{VP.lookup∘tabulate}.

%TC:ignore
\begin{code}
  lookup∘tabulate :  ∀ {a n} {A : Set a} {f : Fin n → Fin n → A} i j →
                     lookup i j (tabulate f) ≡ f i j
  lookup∘tabulate {f = f} i j = begin
    V.lookup j (V.lookup i (V.tabulate (V.tabulate ∘ f)))
      ≡⟨ P.cong (V.lookup j) (VP.lookup∘tabulate (V.tabulate ∘ f) i) ⟩
    V.lookup j (V.tabulate (f i))
      ≡⟨ VP.lookup∘tabulate (f i) j ⟩
    f i j ∎
\end{code}
%TC:endignore

% We begin by defining an equivalence relation between matrices.\footnote{To be precise, \AgdaDatatype{Pointwise} \AgdaDatatype{\_\sim\_} is just a relation for now. The proof that it \emph{is} an equivalence relation provided that \AgdaDatatype{\_\sim\_} is one is given in \cref{Semi-Proofs}.} It is defined by pointwise equivalence of the elements of two matrices of the same shape.

The intuition for this definition is this: in order to show that the \AgdaDatatype{Pointwise} \AgdaDatatype{\_\sim\_} relation holds between two matrices, we must give a function which, for any row index \AgdaBound{r} and any column index \AgdaBound{c}, produces evidence that the relation \AgdaDatatype{\_\sim\_} holds between the elements of the two matrices at this point.

%TC:ignore
\begin{code}
  Pointwise :  ∀ {s t ℓ} {S : Set s} {T : Set t} (_∼_ : REL S T ℓ)
               {m n} → Matrix S m n → Matrix T m n → Set ℓ
  Pointwise _~_ A B = ∀ r c → A [ r , c ] ~ B [ r , c ]
\end{code}
%TC:endignore

%TC:ignore
\begin{code}
  PW-isEquivalence :  ∀ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} {m n} →
                      IsEquivalence _~_ → IsEquivalence (Pointwise _~_ {m = m} {n})
  PW-isEquivalence {_~_ = ~} eq = record { refl = PW-refl ; sym = PW-sym ; trans = PW-trans }
    where
      open IsEquivalence eq

      PW-refl : Reflexive (Pointwise ~)
      PW-refl = (λ r c → refl)

      PW-sym : Symmetric (Pointwise ~)
      PW-sym eq = (λ r c → sym (eq r c))

      PW-trans : Transitive (Pointwise ~)
      PW-trans eq₁ eq₂ = (λ r c → trans (eq₁ r c) (eq₂ r c))
\end{code}
%TC:endignore

Let us consider symmetry in more detail. The property \AgdaFunction{Symmetric} \AgdaDatatype{\_≋\_} is defined as \AgdaSymbol{∀}~\AgdaSymbol{\{}\AgdaBound{A} \AgdaBound{B}\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{B} \AgdaSymbol{→} \AgdaBound{B} \AgdaDatatype{≋} \AgdaBound{A}. That is, it transforms evidence of \AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{B} into evidence that \AgdaBound{B} \AgdaDatatype{≋} \AgdaBound{A}. Since \AgdaDatatype{\_≋\_} has only one constructor, any evidence \AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{B} must be of the form \AgdaInductiveConstructor{ext} \AgdaBound{app} with \AgdaBound{app} \AgdaSymbol{:} \AgdaSymbol{∀} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≈} \AgdaBound{B} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}. This allows us to pattern match on the argument to \AgdaFunction{≋-sym} to extract \AgdaBound{app}.

In order to construct an element of \AgdaBound{B} \AgdaDatatype{≋} \AgdaBound{A}, we must supply the constructor \AgdaInductiveConstructor{ext} with a function of type \AgdaSymbol{∀} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaBound{B} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≈} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}. This can be achieved by abstracting over \AgdaBound{r} and \AgdaBound{c} and then applying the symmetry law of the underlying equivalence \AgdaFunction{sym} to \AgdaBound{app} \AgdaBound{r} \AgdaBound{c} like so:
\begin{align*}
\text{\AgdaSymbol{λ} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaBound{app} \AgdaBound{r} \AgdaBound{c}}
  &\;\AgdaSymbol{:}\; \text{\AgdaSymbol{∀} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≈} \AgdaBound{B} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}} \\
\text{\AgdaSymbol{λ} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaFunction{sym} \AgdaSymbol{(}\AgdaBound{app} \AgdaBound{r} \AgdaBound{c}\AgdaSymbol{)}}
  &\;\AgdaSymbol{:}\; \text{\AgdaSymbol{∀} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaBound{B} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≈} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}} \\
\text{\AgdaInductiveConstructor{ext} \AgdaSymbol{(}\AgdaSymbol{λ} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaFunction{sym} \AgdaSymbol{(}\AgdaBound{app} \AgdaBound{r} \AgdaBound{c}\AgdaSymbol{))}}
  &\;\AgdaSymbol{:}\; \text{\AgdaBound{B} \AgdaDatatype{≋} \AgdaBound{A}} \\
\end{align*}
Our symmetry proof for \AgdaDatatype{\_≋\_} is thus

\[\text{
\AgdaFunction{≋-sym} \AgdaSymbol{(}\AgdaInductiveConstructor{ext} \AgdaBound{app}\AgdaSymbol{)} \AgdaSymbol{=} \AgdaInductiveConstructor{ext} \AgdaSymbol{(λ} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaFunction{sym} \AgdaSymbol{(}\AgdaBound{app} \AgdaBound{r} \AgdaBound{c}\AgdaSymbol{))}
}\]

Reflexivity and transitivity are proved in a similar fashion.

\section{Differences to big operators in Coq}

\chapter{Square matrices over semirings}

% XXX Things that will have to be explained for this chapter to make sense:
% Fin; ∀-notation; open ... using notation; all the lemmas in Bigop.Properties; ℕ and Fin; pattern matching; the Matrix library (representation as Vec of Vecs; tabulate; lookup; syntax); universe levels and ⊔; REL A B ℓ; implicit arguments; records (constructors and fields); how algebraic structures publicly export / import the properties of their substructures; equational reasoning; propositional equality implies any other kind of equivalence via `reflexive`; binary operators and mixfix operators _⊕_ and _[_,_]

In this chapter we present a proof that square matrices over a semiring themselves form a semiring.

\cref{Semi-Defs} introduces various definitions. In \cref{Semi-Plus} we show that square matrices and matrix addition constitute a commutative monoid with an annihilator. \cref{Semi-Times} proves that square matrices and matrix multiplication form a monoid. In \cref{Semi-Distr} we show that matrix multiplication distributes over matrix addition.


\section{\label{Semi-Defs}Definitions}

In this section, we define matrix addition and multiplication, the zero matrix and the identity matrix.

All the code in this chapter resides in a module that is parameterised over the size \AgdaBound{n} of the matrices and the underlying semiring. This has the effect of fixing the variables \AgdaBound{n}, \AgdaBound{c}, \AgdaBound{ℓ} and \AgdaBound{semiring} in the module's body.

%TC:ignore
\AgdaHide{
\begin{code}
open import Algebra
open import Data.Nat.Base using (ℕ; z≤n)
\end{code}
}
\begin{code}
module SemiringProof (n : ℕ) {c ℓ} (semiring : Semiring c ℓ) where
\end{code}
\AgdaHide{
\begin{code}
  open import Bigop
  open import Matrix

  open import Algebra.FunctionProperties
  open import Algebra.Structures
  open import Data.Empty
  open import Data.Fin using (Fin) renaming (zero to zeroF; suc to sucF)
  open import Data.Fin.Properties using (bounded)
  import Data.List.Base as L using ([_])
  open import Data.Product using (proj₁; proj₂; _,_; uncurry)
  open import Function
  open import Function.Equivalence as Equiv using (_⇔_)
  open import Level using (_⊔_)
  open import Relation.Nullary
  open import Relation.Unary
  open import Relation.Binary.Core using (_≡_; _≢_)
  open import Relation.Binary
  import Relation.Binary.Vec.Pointwise as PW
  import Relation.Binary.PropositionalEquality as P

  l∘t = lookup∘tabulate
\end{code}
}
%TC:endignore

We bring the underlying semiring with its carrier type, special elements, operators and substructures into scope. Here \emph{substructures} refers to the weaker structures that can automatically be derived from the a given algebraic structure by subtracting properties, operators or special elements. For example, any commutative monoid gives rise to a monoid if we take away the commutative law.

Semirings contain many induced substructures. In the following, the ones we are interested in are brought into scope explicitly: the commutative monoid, monoid and semigroup over \AgdaFunction{\_+\_}; the monoid and semigroup over \AgdaFunction{\_*\_}; and the \enquote{semiring without one} (a semiring-like structure without an identity for \AgdaFunction{\_*\_}).

%TC:ignore
\begin{code}
  open Semiring semiring
    using     ( Carrier
              ; 0#; 1#; _+_; _*_
              ; setoid
              ; +-semigroup; +-monoid; +-commutativeMonoid
              ; *-semigroup; *-monoid; semiringWithoutOne)
\end{code}
%TC:endignore

Next, the equivalence relation \AgdaDatatype{\_≈\_} of the underlying setoid and its reflexive, symmetric and transitive laws (\AgdaField{refl}, \AgdaField{sym}, \AgdaField{trans}) are brought into scope. We make the sum syntax from the \AgdaModule{Bigop.Core.Fold} module available and open the modules containing lemmas about ordinals, equational reasoning functionality in the element setoid and the module for equational reasoning with propositional equality.

%TC:ignore
\begin{code}
  open Setoid setoid using (_≈_; refl; sym; trans; reflexive; isEquivalence)
  open Fold +-monoid using (Σ-syntax)
  open Props.Ordinals

  open import Relation.Binary.EqReasoning setoid
  open P.≡-Reasoning
    renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)
\end{code}

\AgdaHide{
\begin{code}
  ι = fromLenF 0
\end{code}
}
%TC:endignore

We define \AgdaDatatype{M} as a shorthand for the type of square matrices of size \AgdaBound{n} over the carrier of the underlying semiring and give the pointwise lifting of the equivalence relation between elements the name \AgdaFunction{\_≋\_}. \AgdaDatatype{Matrix} and \AgdaDatatype{Pointwise} are defined in \cref{Impl-Matrices}.

%TC:ignore
\begin{code}
  M : Set c
  M = Matrix Carrier n n

  _≋_ : Rel M ℓ
  _≋_ = Pointwise _≈_
\end{code}
%TC:endignore

Next, we define matrix addition \AgdaFunction{\_⊕\_} and multiplication \AgdaFunction{\_⊗\_}. Addition works pointwise. The function \AgdaFunction{tabulate} populates a matrix using a function that takes the row and column index to an element of the matrix by applying that function to each position in the matrix. It is defined in \cref{Impl-Matrices}.

%TC:ignore
\begin{code}
  _⊕_ : M → M → M
  A ⊕ B = tabulate (λ r c → A [ r , c ] + B [ r , c ])
\end{code}
%TC:endignore

Using Σ-syntax, multiplication can be defined in a concise way.

%TC:ignore
\begin{code}
  mult : M → M → Fin n → Fin n → Carrier
  mult A B r c = Σ[ i ← ι n ] A [ r , i ] * B [ i , c ]

  _⊗_ : M → M → M
  A ⊗ B = tabulate (mult A B)
\end{code}
%TC:endignore

Note how the definition of \AgdaFunction{mult} resembles the component-wise definition of matrix multiplication in standard mathematical notation, \[(A\,B)_{r,c} = \sum_{i ← ι\ n} A_{r,i}\,B_{i,c}\]

The matrix \AgdaFunction{0M} is the identity for matrix addition and the annihilator for matrix multiplication. All of its elements are set to the zero element of the underlying semiring.

%TC:ignore
\begin{code}
  0M : M
  0M = tabulate (λ r c → 0#)
\end{code}
%TC:endignore

\AgdaFunction{1M} is the identity for matrix multiplication. Its definition relies on the function \AgdaFunction{diag}, which returns \AgdaBound{1\#} if its arguments are equal and \AgdaBound{0\#} if they are different.

%TC:ignore
\begin{code}
  diag : {n : ℕ} → Fin n → Fin n → Carrier
  diag  zeroF     zeroF     =  1#        -- r ≡ c
  diag  zeroF     (sucF c)  =  0#        -- r ≢ c
  diag  (sucF r)  zeroF     =  0#        -- r ≢ c
  diag  (sucF r)  (sucF c)  =  diag r c  -- recursive case

  1M : M
  1M = tabulate diag
\end{code}
%TC:endignore

Note that there are many ways to define the function \AgdaFunction{diag}. One alternative would be to use an explicit equality test. The inductive definition given above turned out to be easiest to work with in proofs.

\section{\label{Semi-Plus}Properties of matrix addition}

In this section, we demonstrate that matrix addition is a commutative monoid by proving congruence, associativity and commutativity and showing that \AgdaFunction{0M} is its identity.


\minisec{Congruence}

Usually in mathematical reasoning, we expect that replacing a subterm \(S\) by an equivalent subterm \(S′\) within a term \(T\) gives a term \(T[S′/S]\) that is equivalent to the original term, so \(S ≈ S′ ⇒ T ≈ T[S′/S]\). A special case of this is \(T = f(S)\) for some function \(f\). In a formal system like Agda, the \(f\)-property \(S ≈ S′ ⇒ f(S) ≈ f(S′)\) is called \emph{congruence} or \emph{preservation of equivalence} and must be proved for each function.

Here we prove that matrix addition preserves equivalence, that is, \(A ≋ A′ ∧ B ≋ B′ ⇒ A ⊕ B ≋ A′ ⊕ B′\).

%TC:ignore
\begin{code}
  ⊕-cong : ∀ {A A′ B B′} → A ≋ A′ → B ≋ B′ → (A ⊕ B) ≋ (A′ ⊕ B′)
  ⊕-cong {A} {A′} {B} {B′} eq₁ eq₂ = λ r c → begin
    (A ⊕ B) [ r , c ]             ≡⟨ l∘t r c ⟩
    A [ r , c ]   + B [ r , c ]   ≈⟨ +-cong (eq₁ r c) (eq₂ r c) ⟩
    A′ [ r , c ]  + B′ [ r , c ]  ≡⟨ P.sym (l∘t r c) ⟩
    (A′ ⊕ B′) [ r , c ]           ∎
    where
      open Semigroup +-semigroup using () renaming (∙-cong to +-cong)
\end{code}
%TC:endignore

Since the only law used in this proof is \AgdaFunction{+-assoc}, the semigroup over \AgdaFunction{\_+\_} induced by the underlying semiring is sufficient to prove that matrix addition is associative.


\minisec{Associativity}

Our first algebraic proof shows that matrix addition is associative, that is, \((A ⊕ B) ⊕ C ≋ A ⊕ (B ⊕ C)\). Since matrix addition is defined as elementwise addition, the proof of elementwise equivalence is straightforward: unfold the definition of \AgdaFunction{\_⊕\_}; use associativity of the elementwise addition \AgdaFunction{\_+\_}; fold back into matrix addition.

The auxiliary functions \AgdaFunction{factorˡ} and \AgdaFunction{factorʳ} simply unfold the nested matrix additions.

%TC:ignore
\begin{code}
  ⊕-assoc : Associative _≋_ _⊕_
  ⊕-assoc A B C = λ r c → begin
    ((A ⊕ B) ⊕ C) [ r , c ]                     ≡⟨ factorˡ r c ⟩
    (A [ r , c ] +  B [ r , c ]) + C [ r , c ]  ≈⟨ +-assoc _ _ _ ⟩
    A [ r , c ] + (B [ r , c ]  + C [ r , c ])  ≡⟨ P.sym (factorʳ r c) ⟩
    (A ⊕ (B ⊕ C)) [ r , c ]                     ∎
    where
      open Semigroup +-semigroup using () renaming (assoc to +-assoc)

      factorˡ : ∀ r c → ((A ⊕ B) ⊕ C) [ r , c ] ≡ (A [ r , c ] + B [ r , c ]) + C [ r , c ]
      factorˡ r c = l∘t r c ⟨ P.trans ⟩ P.cong₂ _+_ (l∘t r c) P.refl

      factorʳ : ∀ r c → (A ⊕ (B ⊕ C)) [ r , c ] ≡ A [ r , c ] + (B [ r , c ] + C [ r , c ])
      factorʳ r c = l∘t r c ⟨ P.trans ⟩ P.cong₂ _+_ P.refl (l∘t r c)
\end{code}
%TC:endignore

The structure of the proof is similar to the congruence proof above. Again, a semigroup over \AgdaFunction{\_+\_} provides sufficient structure.


\minisec{Left identity}

%TC:ignore
\begin{code}
  ⊕-identityˡ : LeftIdentity _≋_ 0M _⊕_
  ⊕-identityˡ A = λ r c → begin
    (0M ⊕ A) [ r , c ]           ≡⟨ l∘t r c ⟩
    0M [ r , c ] +  A [ r , c ]  ≡⟨ P.cong₂ _+_ (l∘t r c) P.refl ⟩
              0# +  A [ r , c ]  ≈⟨ proj₁ +-identity _ ⟩
                    A [ r , c ]  ∎
    where
      open Monoid +-monoid using () renaming (identity to +-identity)
\end{code}
%TC:endignore

\minisec{Commutativity of matrix addition}

%TC:ignore
\begin{code}
  ⊕-comm : Commutative _≋_ _⊕_
  ⊕-comm A B = λ r c → begin
    (A ⊕ B) [ r , c ]           ≡⟨ l∘t r c ⟩
    A [ r , c ]  + B [ r , c ]  ≈⟨ +-comm _ _ ⟩
    B [ r , c ]  + A [ r , c ]  ≡⟨ P.sym (l∘t r c) ⟩
    (B ⊕ A) [ r , c ]           ∎
    where
      open CommutativeMonoid +-commutativeMonoid using ()
        renaming (comm to +-comm)
\end{code}
%TC:endignore

\section{\label{Semi-Times}Properties of matrix multiplication}

\minisec{Left zero for matrix multiplication}

In this proof that \AgdaFunction{0M} is the left zero for \AgdaFunction{\_⊗\_}, that is, \AgdaFunction{0M} \AgdaFunction{⊗} \AgdaBound{A} \AgdaDatatype{≋} \AgdaFunction{0M}, we use two lemmas from \AgdaModule{Bigop.Properties} for the first time.

As described in XXX, \AgdaFunction{Σ.cong} states that if lists \AgdaBound{is} and \AgdaBound{js} are propositionally equal and functions \AgdaBound{f} and \AgdaBound{g} are extensionally equal with respect to \AgdaDatatype{\_≈\_}, then \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{is} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{j} \AgdaFunction{←} \AgdaBound{js} \AgdaFunction{]} \AgdaBound{g} \AgdaBound{j}.

%TC:ignore
\begin{code}
  M-zeroˡ : LeftZero _≋_ 0M _⊗_
  M-zeroˡ A = λ r c → begin
    (0M ⊗ A) [ r , c ]                       ≡⟨ l∘t r c ⟩
    Σ[ i ← ι n ] 0M [ r , i ] * A [ i , c ]
      ≈⟨ Σ.cong  (ι n) P.refl
                 (λ i → reflexive (l∘t r i) ⟨ *-cong ⟩ refl) ⟩
    Σ[ i ← ι n ] 0# * A [ i , c ]            ≈⟨ sym (Σ.distrˡ _ 0# (ι n)) ⟩
    0# * (Σ[ i ← ι n ] A [ i , c ])          ≈⟨ proj₁ zero _ ⟩
    0#                                       ≡⟨ P.sym (l∘t r c) ⟩
    0M [ r , c ]                             ∎
    where
      open SemiringWithoutOne semiringWithoutOne using (*-cong; zero)
      module Σ = Props.SemiringWithoutOne semiringWithoutOne using (cong; distrˡ)
\end{code}
%TC:endignore

Let us consider the second step of the proof in detail. The aim is to use \AgdaFunction{Σ.cong} to show that
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaFunction{ι} \AgdaBound{n} \AgdaFunction{]} \AgdaFunction{0M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}
\AgdaDatatype{≈}
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaFunction{ι} \AgdaBound{n} \AgdaFunction{]} \AgdaFunction{0\#} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}.

On both sides of the equivalence, we take the sum over \AgdaSymbol{(}\AgdaFunction{ι} \AgdaBound{n}\AgdaSymbol{)}. The proof that the lists are propositionally equal is therefore just \AgdaInductiveConstructor{P.refl}.

We now need to prove that \AgdaFunction{0M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≈} \AgdaFunction{0\#} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} for all \AgdaBound{i}. The outer form of this expression is a multiplication. Since our goal is to replace equal subterms by equal subterms, we need to use the appropriate congruence rule, \AgdaFunction{*-cong}. The right hand sides of the two multiplications are both \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}, so they are trivially equivalent by \AgdaFunction{refl}.

\AgdaFunction{0M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} is propositionally equal to \AgdaFunction{0\#} by (\AgdaFunction{l∘t} \AgdaBound{r} \AgdaBound{i}). Equivalence in \AgdaDatatype{\_≈\_} follows from propositional equality by \AgdaFunction{reflexivity}, which proves that the left hand sides of the multiplications are ≈-equivalent too.

Putting this all together, we have built a term
\[ \text{\AgdaFunction{Σ.cong} \AgdaSymbol{(}\AgdaFunction{ι} \AgdaBound{n}\AgdaSymbol{)} \AgdaInductiveConstructor{P.refl} \AgdaSymbol{(λ} \AgdaBound{i} \AgdaSymbol{→} \AgdaFunction{reflexive} \AgdaSymbol{(}\AgdaFunction{l∘t} \AgdaBound{r} \AgdaBound{i}\AgdaSymbol{)} \AgdaFunction{⟨} \AgdaFunction{*-cong} \AgdaFunction{⟩} \AgdaFunction{refl}\AgdaSymbol{)} \AgdaFunction{⟩}} \]
proving

\[ \text{\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaFunction{ι} \AgdaBound{n} \AgdaFunction{]} \AgdaFunction{0M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}
\AgdaDatatype{≈}
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaFunction{ι} \AgdaBound{n} \AgdaFunction{]} \AgdaFunction{0\#} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}} \]

In the remainder of the proof, we first multiply out the \AgdaFunction{0\#} using distributivity and then apply the \AgdaFunction{zero} law of the underlying semiring.


\minisec{Right-zero of matrix multiplication}

%TC:ignore
\AgdaHide{
\begin{code}
  M-zeroʳ : RightZero _≋_ 0M _⊗_
  M-zeroʳ A = λ r c → begin
    (A ⊗ 0M) [ r , c ]               ≡⟨ l∘t r c ⟩
    Σ[ i ← ι n ] A [ r , i ] * 0M [ i , c ]
      ≈⟨ Σ.cong  (ι n) P.refl
                 (λ i → *-cong refl (reflexive (l∘t i c))) ⟩
    Σ[ i ← ι n ] A [ r , i ] * 0#    ≈⟨ sym (Σ.distrʳ _ 0# (ι n)) ⟩
    (Σ[ i ← ι n ] A [ r , i ]) * 0#  ≈⟨ proj₂ zero _ ⟩
    0#                               ≡⟨ P.sym (l∘t r c) ⟩
    0M [ r , c ] ∎
    where
      open SemiringWithoutOne semiringWithoutOne using (*-cong; zero)
      module Σ = Props.SemiringWithoutOne semiringWithoutOne
\end{code}
}
%TC:endignore

\minisec{Associativity of matrix multiplication}

This proof is more involved than the associativity proof for matrix addition. The argument runs as follows:

\begin{align}
((A ⊗ B) ⊗ C)_{r,c}
&≈ \sum_{i\,←\,ι\,n} \left( \sum_{j\,←\,ι\,n} A_{r,j}\, B_{j,i} \right) C_{i,c}
    && \text{by the definition of ⊗} \\
&≈ \sum_{i\,←\,ι\,n} \sum_{j\,←\,ι\,n} (A_{r,j}\, B_{j,i}) C_{i,c}
    && \text{by right-distributivity} \\
&≈ \sum_{j\,←\,ι\,n} \sum_{i\,←\,ι\,n} (A_{r,j}\, B_{j,i}) C_{i,c}
    && \text{swapping the outer sums} \\
&≈ \sum_{j\,←\,ι\,n} \sum_{i\,←\,ι\,n} A_{r,j}\, (B_{j,i}\, C_{i,c})
    && \text{by associativity} \\
&≈ \sum_{j\,←\,ι\,n} A_{r,j} \sum_{i\,←\,ι\,n} B_{j,i}\, C_{i,c}
    && \text{by left-distributivity} \\
&≈ (A ⊗ (B ⊗ C))_{r,c}
    && \text{by the definition of ⊗}
\end{align}

In the Agda proof, we use the appropriate congruence rules to replace subterms by equivalent subterms. Steps (3.4) and (3.5) have been factored into a separate function \AgdaFunction{inner} to make the proof more readable.

%TC:ignore
\begin{code}
  ⊗-assoc : Associative _≋_ _⊗_
  ⊗-assoc A B C = λ r c → begin
{- 3.1 -}  ((A ⊗ B) ⊗ C) [ r , c ]                                              ≈⟨ factorˡ r c ⟩
{- 3.2 -}  Σ[ i ← ι n ] (Σ[ j ← ι n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]
             ≈⟨ Σ.cong (ι n) P.refl (λ i → Σ.distrʳ _ _ (ι n)) ⟩
{- 3.3 -}  Σ[ i ← ι n ] Σ[ j ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]  ≈⟨ Σ.swap _ (ι n) (ι n) ⟩
           Σ[ j ← ι n ] Σ[ i ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
             ≈⟨ Σ.cong (ι n) P.refl (inner r c) ⟩
{- 3.6 -}  Σ[ j ← ι n ] A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ])  ≈⟨ sym $ factorʳ r c ⟩
           (A ⊗ (B ⊗ C)) [ r , c ]                                               ∎
    where
      open SemiringWithoutOne semiringWithoutOne using (*-assoc; *-cong)
      module Σ = Props.SemiringWithoutOne semiringWithoutOne
        using (cong; swap; distrˡ; distrʳ)

      inner : ∀ r c j →  Σ[ i ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ] ≈
                         A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ])
      inner r c j = begin
{- 3.4 -}  Σ[ i ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]  ≈⟨ Σ.cong (ι n) P.refl (λ i → *-assoc _ _ _) ⟩
{- 3.5 -}  Σ[ i ← ι n ] A [ r , j ] * (B [ j , i ] * C [ i , c ])  ≈⟨ sym (Σ.distrˡ _ _ (ι n)) ⟩
           A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ])   ∎

      factorˡ : ∀ r c →  ((A ⊗ B) ⊗ C) [ r , c ] ≈
                         Σ[ i ← ι n ] (Σ[ j ← ι n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]
      factorˡ r c = reflexive (l∘t r c) ⟨ trans ⟩
                    Σ.cong (ι n) P.refl (λ i → *-cong (reflexive (l∘t r i)) refl)

      factorʳ : ∀ r c →  (A ⊗ (B ⊗ C)) [ r , c ] ≈
                         Σ[ j ← ι n ] A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ])
      factorʳ r c = reflexive (l∘t r c) ⟨ trans ⟩
                    Σ.cong (ι n) P.refl (λ j → *-cong refl (reflexive (l∘t j c)))
\end{code}
%TC:endignore

\minisec{Congruence of matrix multiplication}
%TC:ignore
\begin{code}
  ⊗-cong : _⊗_ Preserves₂ _≋_ ⟶ _≋_ ⟶ _≋_
  ⊗-cong {A} {A′} {B} {B′} eq₁ eq₂ = λ r c → begin
    (A ⊗ B) [ r , c ]
       ≡⟨ l∘t r c ⟩
    Σ[ i ← ι n ] A [ r , i ] * B [ i , c ]
       ≈⟨ Σ.cong (ι n) P.refl (λ i → *-cong (eq₁ r i) (eq₂ i c)) ⟩
    Σ[ i ← ι n ] A′ [ r , i ] * B′ [ i , c ]
       ≡⟨ P.sym (l∘t r c) ⟩
    (A′ ⊗ B′) [ r , c ] ∎
    where
      open Semigroup *-semigroup using () renaming (∙-cong to *-cong)
      module Σ = Props.Monoid +-monoid using (cong)
\end{code}
%TC:endignore


\minisec{Left identity for matrix multiplication}

This is the longest of the semiring proofs. We show that \AgdaFunction{1M} \AgdaFunction{⊗} \AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{A} for all \AgdaBound{A}. The key idea here is that for any term involving \AgdaFunction{1M}, it makes sense to case split on whether the row \AgdaBound{r} and column \AgdaBound{c} are equal. If they are, then \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{1\#} by \AgdaFunction{1M-diag}. If not, then by \AgdaFunction{1M-∁-diag} we have \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{0\#}.

(make this fit in BEGIN)
The next two lemmas show that the elements of the identity matrix \AgdaFunction{1M} are equal to \AgdaFunction{1\#} on the diagonal and \AgdaFunction{0\#} everywhere else.

%TC:ignore
\begin{code}
  1M-diag : ∀ {r c} → r ≡ c → 1M [ r , c ] ≡ 1#
  1M-diag {r} {.r} P.refl = start
    1M [ r , r ]  ≣⟨ l∘t r r ⟩
    diag r r      ≣⟨ diag-lemma r ⟩
    1#            □
      where
        diag-lemma  : ∀ {n} (r : Fin n) → diag r r ≡ 1#
        diag-lemma  zeroF     =  P.refl
        diag-lemma  (sucF r)  =  diag-lemma r
\end{code}
%TC:endignore

lala

%TC:ignore
\begin{code}
  1M-∁-diag  : ∀ {r c} → ∁ (_≡_ r) c → 1M [ r , c ] ≡ 0#
  1M-∁-diag  {r} {c}   eq  with ≟ r c
  1M-∁-diag  {r} {.r}  ¬eq  | yes  P.refl  = ⊥-elim (¬eq P.refl)
  1M-∁-diag  {r} {c}   ¬eq  | no   _       = start
    1M [ r , c ]  ≣⟨ l∘t r c ⟩
    diag r c      ≣⟨ diag-lemma r c ¬eq ⟩
    0#            □
      where
        suc-¬-lemma  : ∀ {n} {r c : Fin n} → ¬ sucF r ≡ sucF c → ¬ r ≡ c
        suc-¬-lemma  {r} ¬eq P.refl = ¬eq P.refl

        diag-lemma  : ∀ {n} (r c : Fin n) → ¬ r ≡ c → diag r c ≡ 0#
        diag-lemma  zeroF     zeroF     ¬eq  =  ⊥-elim (¬eq P.refl)
        diag-lemma  zeroF     (sucF _)  _    =  P.refl
        diag-lemma  (sucF r)  zeroF     ¬eq  =  P.refl
        diag-lemma  (sucF r)  (sucF c)  ¬eq  =  diag-lemma r c (suc-¬-lemma ¬eq)
\end{code}
%TC:endignore

(make this fit in END)

In \AgdaFunction{ident}, after unfolding the definition of \AgdaFunction{⊗}, we split the list (\AgdaFunction{ι} \AgdaBound{n}) that is being summed over by the decidable predicate (\AgdaFunction{≟} \AgdaBound{r}) using \AgdaFunction{Σ.split-P}. This lets us consider the cases \AgdaBound{r} \AgdaFunction{≡} \AgdaBound{i} and \AgdaBound{r} \AgdaFunction{≢} \AgdaBound{i} separately.

The function \AgdaFunction{≡-step} deals with the first case. From \AgdaBound{r} \AgdaFunction{≡} \AgdaBound{i} follows \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{1\#}. Using distributivity and the identity law for \AgdaFunction{\_*\_}, we can deduce that

\[ \text{
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaFunction{ι} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{≟} \AgdaBound{r} \AgdaFunction{]} \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaFunction{≈}
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaFunction{ι} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{≟} \AgdaBound{r} \AgdaFunction{]} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}
}\]

Otherwise, \AgdaFunction{≢-step} assumes that \AgdaBound{r} \AgdaFunction{≢} \AgdaBound{i}. It follows that \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{0\#}. By distributivity and the \AgdaFunction{zero} law of the underlying semiring we then have

\[ \text{
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaFunction{ι} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{∁′} (\AgdaFunction{≟} \AgdaBound{r}) \AgdaFunction{]} \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaFunction{≈}
\AgdaFunction{0\#}
}\]

XXX discuss \AgdaFunction{filter} and \AgdaFunction{ordinals-filterF}.

%TC:ignore
\begin{code}
  ⊗-identityˡ : LeftIdentity _≋_ 1M _⊗_
  ⊗-identityˡ A = λ r c → begin
    (1M ⊗ A) [ r , c ]                                     ≡⟨ l∘t r c ⟩
    Σ[ i ← ι n ] 1M [ r , i ] * A [ i , c ]                ≈⟨ Σ.split-P _ (ι n) (≟ r) ⟩
    Σ[ i ← ι n ∥ ≟ r ]       1M [ r , i ] * A [ i , c ] +
    Σ[ i ← ι n ∥ ∁′ (≟ r) ]  1M [ r , i ] * A [ i , c ]    ≈⟨ ≡-step r c ⟨ +-cong ⟩ ≢-step r c ⟩
    Σ[ i ← ι n ∥ ≟ r ] A [ i , c ] + 0#                    ≈⟨ proj₂ +-identity _ ⟩
    Σ[ i ← ι n ∥ ≟ r ] A [ i , c ]                         ≡⟨ P.cong  (Σ-syntax (λ i → A [ i , c ]))
                                                                      (filter r c) ⟩
    A [ r , c ] + 0#                                       ≈⟨ proj₂ +-identity _  ⟩
    A [ r , c ]                                            ∎
    where
      open Semiring semiring using (+-cong; +-identity; *-cong; *-identity; zero)
      module Σ = Props.SemiringWithoutOne semiringWithoutOne
        using (cong-P; split-P; distrˡ)

      ≡-step : ∀ r c →  Σ[ i ← ι n ∥ ≟ r ] 1M [ r , i ] * A [ i , c ] ≈
                        Σ[ i ← ι n ∥ ≟ r ] A [ i , c ]
      ≡-step r c = begin
        Σ[ i ← ι n ∥ ≟ r ] 1M [ r , i ] * A [ i , c ]
          ≈⟨ Σ.cong-P  (ι n) (≟ r)
                       (λ i r≡i → reflexive (1M-diag r≡i) ⟨ *-cong ⟩ refl) ⟩
        Σ[ i ← ι n ∥ ≟ r ] 1# * A [ i , c ]    ≈⟨ sym $ Σ.distrˡ _ 1# (ι n ∥ ≟ r) ⟩
        1# * (Σ[ i ← ι n ∥ ≟ r ] A [ i , c ])  ≈⟨ proj₁ *-identity _ ⟩
        Σ[ i ← ι n ∥ ≟ r ] A [ i , c ]         ∎

      ≢-step : ∀ r c → Σ[ i ← ι n ∥ ∁′ (≟ r) ] 1M [ r , i ] * A [ i , c ] ≈ 0#
      ≢-step r c = begin
        Σ[ i ← ι n ∥ ∁′ (≟ r) ] 1M [ r , i ] * A [ i , c ]
          ≈⟨ Σ.cong-P  (ι n) (∁′ (≟ r))
                       (λ i r≢i → reflexive (1M-∁-diag r≢i) ⟨ *-cong ⟩ refl) ⟩
        Σ[ i ← ι n ∥ ∁′ (≟ r) ] 0# * A [ i , c ]      ≈⟨ sym $ Σ.distrˡ _ 0# (ι n ∥ ∁′ (≟ r)) ⟩
        0# * (Σ[ i ← ι n ∥ (∁′ (≟ r)) ] A [ i , c ])  ≈⟨ proj₁ zero _ ⟩
        0#                                            ∎

      filter : ∀ r c → ι n ∥ ≟ r ≡ L.[ r ]
      filter r c = ordinals-filterF z≤n (bounded r)
\end{code}
%TC:endignore

%TC:ignore
\AgdaHide{
\begin{code}
  ⊗-identityʳ : RightIdentity _≋_ 1M _⊗_
  ⊗-identityʳ A = ident
    where
      open Semiring semiring using (+-cong; +-identity; *-cong; *-identity; zero)
      module Σ = Props.SemiringWithoutOne semiringWithoutOne

      ∁-sym : ∀ {a} {A : Set a} {A B : A} → ∁ (_≡_ A) B → ∁ (λ C → B ≡ C) A
      ∁-sym eq P.refl = eq P.refl

      ident : ∀ r c → (A ⊗ 1M) [ r , c ] ≈ A [ r , c ]
      ident r c = begin
        (A ⊗ 1M) [ r , c ]
          ≡⟨ l∘t r c ⟩
        Σ[ i ← ι n ] A [ r , i ] * 1M [ i , c ]
          ≈⟨ Σ.split-P _ (ι n) (≟ c) ⟩
        Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ] * 1M [ i , c ] +
        Σ[ i ← ι n ∥ ∁′ (≟ c) ] A [ r , i ] * 1M [ i , c ]
          ≈⟨ +-cong
               (Σ.cong-P (ι n) (≟ c)
                         (λ i c≡i → *-cong refl
                                           (reflexive (1M-diag (P.sym c≡i)))))
               (Σ.cong-P (ι n) (∁′ (≟ c))
                         (λ i c≢i → *-cong refl
                                           (reflexive (1M-∁-diag (∁-sym c≢i))))) ⟩
        Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ] * 1# +
        Σ[ i ← ι n ∥ ∁′ (≟ c) ] A [ r , i ] * 0#
          ≈⟨ sym $ +-cong (Σ.distrʳ _ 1# (ι n ∥ (≟ c)))
                          (Σ.distrʳ _ 0# (ι n ∥ ∁′ (≟ c))) ⟩
        (Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ]) * 1# +
        (Σ[ i ← ι n ∥ (∁′ (≟ c)) ] A [ r , i ]) * 0#
          ≈⟨ +-cong (proj₂ *-identity _) (proj₂ zero _) ⟩
        (Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ]) + 0#
          ≈⟨ proj₂ +-identity _ ⟩
        Σ[ i ← ι n ∥ (≟ c) ] A [ r , i ]
          ≡⟨ P.cong (Σ-syntax (λ i → A [ r , i ]))
                    (ordinals-filterF z≤n (bounded c)) ⟩
        Σ[ i ← L.[ c ] ] A [ r , i ]
          ≈⟨ proj₂ +-identity _  ⟩
        A [ r , c ] ∎
\end{code}
}
%TC:endignore

\section{\label{Semi-Distr}Distributivity laws}

\minisec{Left-distributivity}

This proof shows that \AgdaBound{A} \AgdaFunction{⊗} \AgdaSymbol{(}\AgdaBound{B} \AgdaFunction{⊕} \AgdaBound{C}\AgdaSymbol{)} \AgdaDatatype{≋} \AgdaSymbol{(}\AgdaBound{A} \AgdaFunction{⊗} \AgdaBound{B}\AgdaSymbol{)} \AgdaFunction{⊕} \AgdaSymbol{(}\AgdaBound{A} \AgdaFunction{⊗} \AgdaBound{C}\AgdaSymbol{)}. Most of \AgdaFunction{distr} is concerned with unfolding the definition of \AgdaFunction{\_⊕\_} and \AgdaFunction{\_⊗\_}. The crucial step in the proof is the application of the left-distributivity law of the underlying semiring in \AgdaFunction{inner} (1) followed by the use of \AgdaFunction{Σ.merge} in \AgdaFunction{distr} (2), splitting the sum into two.

%TC:ignore
\begin{code}
  ⊗-distrOverˡ-⊕ : (_≋_ DistributesOverˡ _⊗_) _⊕_
  ⊗-distrOverˡ-⊕ A B C = distr
    where
      open Semiring semiring using (*-cong; distrib)
      module Σ = Props.CommutativeMonoid +-commutativeMonoid
        using (cong; merge)

      inner : ∀ r c i → A [ r , i ] * (B ⊕ C) [ i , c ] ≈
                        A [ r , i ] * B [ i , c ] + A [ r , i ] * C [ i , c ]
      inner r c i = begin
          A [ r , i ] * (B ⊕ C) [ i , c ]                        ≈⟨ refl ⟨ *-cong ⟩ reflexive (l∘t i c) ⟩
{- 1 -}   A [ r , i ] * (B [ i , c ] + C [ i , c ])              ≈⟨ proj₁ distrib _ _ _ ⟩
          A [ r , i ] * B [ i , c ] + A [ r , i ] * C [ i , c ]  ∎

      distr : ∀ r c → (A ⊗ (B ⊕ C)) [ r , c ] ≈ ((A ⊗ B) ⊕ (A ⊗ C)) [ r , c ]
      distr r c = begin
          (A ⊗ (B ⊕ C)) [ r , c ]                       ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] A [ r , i ] * (B ⊕ C) [ i , c ]  ≈⟨ Σ.cong (ι n) P.refl (inner r c)⟩
          Σ[ i ← ι n ] (  A [ r , i ] * B [ i , c ] +
{- 2 -}                   A [ r , i ] * C [ i , c ])    ≈⟨ sym $ Σ.merge _ _ (ι n) ⟩
          Σ[ i ← ι n ] A [ r , i ] * B [ i , c ] +
          Σ[ i ← ι n ] A [ r , i ] * C [ i , c ]        ≡⟨ P.sym $ l∘t r c ⟨ P.cong₂ _+_ ⟩ l∘t r c ⟩
          (A ⊗ B) [ r , c ] + (A ⊗ C) [ r , c ]         ≡⟨ P.sym $ l∘t r c ⟩
          ((A ⊗ B) ⊕ (A ⊗ C)) [ r , c ]                 ∎
\end{code}
%TC:endignore

\minisec{Right-distributivity}

%TC:ignore
\AgdaHide{
\begin{code}
  ⊗-distrOverʳ-⊕ : (_≋_ DistributesOverʳ _⊗_) _⊕_
  ⊗-distrOverʳ-⊕ C A B = distr
    where
      open Semiring semiring using (*-cong; distrib)
      module Σ = Props.SemiringWithoutOne semiringWithoutOne

      distr : ∀ r c → ((A ⊕ B) ⊗ C) [ r , c ] ≈ ((A ⊗ C) ⊕ (B ⊗ C)) [ r , c ]
      distr r c = begin
        ((A ⊕ B) ⊗ C) [ r , c ]
          ≡⟨ l∘t r c ⟩
        Σ[ i ← ι n ] (A ⊕ B) [ r , i ] * C [ i , c ]
          ≈⟨ Σ.cong (ι n) P.refl (λ i → begin

            (A ⊕ B) [ r , i ] * C [ i , c ]
              ≈⟨ *-cong (reflexive (l∘t r i)) refl ⟩
            (A [ r , i ] + B [ r , i ]) * C [ i , c ]
              ≈⟨ proj₂ distrib _ _ _ ⟩
            (A [ r , i ] * C [ i , c ]) + (B [ r , i ] * C [ i , c ]) ∎)⟩

        Σ[ i ← ι n ] ((A [ r , i ] * C [ i , c ]) + (B [ r , i ] * C [ i , c ]))
          ≈⟨ sym (Σ.merge _ _ (ι n)) ⟩
        Σ[ i ← ι n ] A [ r , i ] * C [ i , c ] +
        Σ[ i ← ι n ] B [ r , i ] * C [ i , c ]
          ≡⟨ P.sym $ P.cong₂ _+_ (l∘t r c) (l∘t r c) ⟩
        (A ⊗ C) [ r , c ] + (B ⊗ C) [ r , c ]
          ≡⟨ P.sym (l∘t r c) ⟩
        ((A ⊗ C) ⊕ (B ⊗ C)) [ r , c ] ∎
\end{code}
}
%TC:endignore

\begin{code}
  M-isSemiring : IsSemiring _≋_ _⊕_ _⊗_ 0M 1M
  M-isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isSemigroup = record
          { isEquivalence = ≋-isEquivalence
          ; assoc         = ⊕-assoc
          ; ∙-cong        = ⊕-cong
          }
        ; identityˡ       = ⊕-identityˡ
        ; comm            = ⊕-comm
        }
      ; *-isMonoid = record
        { isSemigroup = record
          { isEquivalence = ≋-isEquivalence
          ; assoc         = ⊗-assoc
          ; ∙-cong        = ⊗-cong
          }
        ; identity        = ⊗-identityˡ , ⊗-identityʳ
        }
      ; distrib           = ⊗-distrOverˡ-⊕ , ⊗-distrOverʳ-⊕
      }
    ; zero                = M-zeroˡ , M-zeroʳ
    }
    where
      ≋-isEquivalence : IsEquivalence _≋_
      ≋-isEquivalence = PW-isEquivalence isEquivalence
\end{code}

\chapter{Evaluation}

\section{Theorems proved}

Binomial theorem

Gauss

\printbibliography

\end{document}
