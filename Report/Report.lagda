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

\begin{document}
\setmathfont{Asana-Math.otf}

\begin{titlepage}
\maketitle
\end{titlepage}

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

This project was implemented in \emph{Agda}, a dependently typed functional programming language. In comparison to non-dependent functional languages like Haskell or ML, the type system is more expressive: it serves as a higher-order logic. The downside is that type inference is incomplete, so most terms need type annotations.

Here we introduce the syntax of the language. The next section explains how Agda can be used to write theorems and proofs.

\minisec{Datatypes and functions}

Truth values (booleans) can be defined in Agda as follows:

%TC:ignore
\begin{code}
  data Bool : Set where
    true   :  Bool
    false  :  Bool
\end{code}
%TC:endignore

\AgdaDatatype{Bool} is a type, so its type (after the colon) is \AgdaPrimitiveType{Set}, the type of (simple) types. \AgdaInductiveConstructor{true} and \AgdaInductiveConstructor{false} are the two constructors for this type.

Let us now write a function using this newly introduced datatype. \AgdaFunction{negate} flips the Boolean passed to it.

%TC:ignore
\begin{code}
  negate : Bool → Bool
  negate true   = false
  negate false  = true
\end{code}
%TC:endignore

Like any top-level function, \AgdaFunction{negate} must be annotated with its type. It takes a \AgdaDatatype{Bool} and returns a \AgdaDatatype{Bool}, so the type of the function as a whole is \AgdaDatatype{Bool} \AgdaSymbol{→} \AgdaDatatype{Bool}. The function is defined by pattern matching: the result of the function is the term on the right-hand side of the equality sign if its input matches the left-hand side.

Note that the pattern matching must cover all possible cases. More generally speaking, all functions must be \emph{total}, that is, defined on all inputs of its argument types.

%TC:ignore
\begin{code}
  _∧_ : Bool → Bool → Bool
  true  ∧ true  = true
  _     ∧ _     = false
\end{code}
%TC:endignore

Agda identifiers can consist of unicode symbols, which makes it possible to use notation familiar from mathematics in Agda code. The function \AgdaFunction{\_∧\_} computes the logical conjunction of its inputs. The underscores in the name of the function indicate where it expects its arguments. This allows Agda programmers to introduce new infix and mixfix operators. As a pattern, the underscore matches anything. The definition of \AgdaFunction{\_∧\_} can thus be read as \enquote{the conjunction of two booleans is true if both arguments are true; in any other case, the result is false.}

A natural number is either zero, or the successor of some natural number. In Agda, this is written as

%TC:ignore
\begin{code}
  data ℕ : Set where
    zero  : ℕ
    suc   : ℕ → ℕ
\end{code}
%TC:endignore

Addition of natural numbers can then be defined as follows.

%TC:ignore
\begin{code}
  _+_ : ℕ → ℕ → ℕ
  zero   + n = n
  suc m  + n = suc (m + n)
\end{code}
%TC:endignore

Note that Agda functions defined on inductive types must not only be total, but also \emph{terminating}. Since termination checking is undecidable, Agda checks whether the arguments to the recursive call are structurally smaller than the arguments to the caller. This is clearly the case in the recursive case of \AgdaFunction{\_+\_}: the arguments to the caller are \AgdaInductiveConstructor{suc} \AgdaBound{m} and \AgdaBound{n} whereas those passed used in the recursive call are \AgdaBound{m} and \AgdaBound{n}. Structurally, \AgdaBound{m} is smaller than \AgdaInductiveConstructor{suc} \AgdaBound{m} so Agda can infer that the function terminates on all inputs.

\minisec{The type hierarchy}

Both \AgdaDatatype{Bool} and \AgdaDatatype{ℕ} as well as all the functions we have seen so far could have been written in a very similar way in Haskell or ML, modulo syntax. We will now see how Agda is different from non-dependent functional languages.

The Agda standard library defines the type of lists like this:

%TC:ignore
\begin{code}
  data List {a : Level} (A : Set a) : Set a where
    []   : List A
    _∷_  : A → List A → List A
\end{code}
%TC:endignore

Let us look at two examples of lists first. \AgdaFunction{bools} is a list of boolean values. The carrier type of the list, \AgdaBound{A}, is instantiated to \AgdaDatatype{Bool}.

%TC:ignore
\begin{code}
  bools : List Bool
  bools = true ∷ (false ∷ ((true ∧ false) ∷ []))
\end{code}
%TC:endignore

In the datatype declaration of \AgdaDatatype{List}, the names \AgdaBound{a} and \AgdaBound{A} are left of the colon. They are shared between the constructors of the datatype and called \emph{parameters}. The parameter \AgdaBound{a} is written in curly braces, which marks it as an \emph{implicit} parameter. This means that Agda will try to infer its value if it is not given explicitly.

The type \AgdaDatatype{Bool} has type \AgdaPrimitiveType{Set}, which is just a synonym for \AgdaPrimitiveType{Set₀}, the type of simple types. Agda correctly infers that \AgdaBound{a} must be \AgdaFunction{zero}. If we wanted to be explicit, we could have written the declaration as \AgdaFunction{bools} \AgdaSymbol{:} \AgdaDatatype{List} \AgdaSymbol{\{}\AgdaFunction{zero}\AgdaSymbol{\}} \AgdaDatatype{Bool} instead.

Why is the parameter \AgdaBound{a} necessary at all? Every type in Agda resides somewhere in the type hierarchy. In other words, if a type \AgdaBound{A} is valid, then there exists some level \AgdaBound{a} such that \AgdaBound{A} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaBound{a}. The reason for introducing a hierarchy of types in the first place is that allowing a typing judgement like \AgdaPrimitiveType{Set} \AgdaSymbol{:} \AgdaPrimitiveType{Set} leads to an inconsistent logic, a phenomenon referred to as \emph{Russel's paradox} in the literature.

Since our definition of \AgdaDatatype{List} abstracts over the level of its carrier type, we can also build lists the live higher up in the type hierarchy. We might for example want to create a list of types.

%TC:ignore
\begin{code}
  types : List Set
  types = Bool ∷ (((ℕ → ℕ) → Bool) ∷ [])
\end{code}
%TC:endignore

Here the carrier type of the list is instantiated as \AgdaPrimitiveType{Set}, which is itself of type \AgdaPrimitiveType{Set₁}. The value of the implicit parameter \AgdaBound{a} is inferred as level one. Note that the function type \AgdaSymbol{(}\AgdaDatatype{ℕ} \AgdaSymbol{→} \AgdaDatatype{ℕ}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{Bool} also lives at level one of the type hierarchy.

\minisec{Dependent types}

We now turn to the classic example of a dependent datatype: fixed-length lists, or \emph{vectors}.

%TC:ignore
\begin{code}
  data Vec {a} (A : Set a) : ℕ → Set a where
    []   : Vec A zero
    _∷_  : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}
%TC:endignore

The parameters (on the left-hand side of the colon in the type declaration) are the same as for \AgdaDatatype{List}, a type level \AgdaBound{a} and a type \AgdaBound{A}. Note that we have not specified the type of \AgdaBound{a}---Agda infers that it must be a level. In addition to the parameters, the type \AgdaDatatype{Vec} is \emph{indexed} by a natural number. This is why there is a \AgdaDatatype{ℕ} on the right-hand side of the colon. While parameters are the same for all constructors, indices may differ: the constructor \AgdaInductiveConstructor{[]} returns a zero-length vector, while \AgdaInductiveConstructor{\_∷\_} takes an element and a vector of length \AgdaBound{n} and returns a vector of length \AgdaInductiveConstructor{suc} \AgdaBound{n}.

The vector append function \AgdaFunction{\_++\_} demonstrates how dependent types can be used to write (partially) verified code. It takes two vectors of length \AgdaBound{m} and \AgdaBound{n}, respectively, and returns a vector of length \AgdaBound{m} \AgdaFunction{+} \AgdaBound{n}. The fact that the type checker accepts the definition of this function means that the length of the vector that is returned really is the sum of the lengths of the input vector, always. This gives us some reassurance that the function does something sensible.

%TC:ignore
\begin{code}
  _++_ :  {a : Level} {m : ℕ} {n : ℕ} → {A : Set a} →
          Vec A m → Vec A n → Vec A (m + n)
  []        ++ ys = ys
  (x ∷ xs)  ++ ys = x ∷ (xs ++ ys)
\end{code}
%TC:endignore

The type declaration of \AgdaFunction{\_++\_} uses three implicit arguments. Their types are completely determined by the way they are used. We can thus shorten the type declaration up to the first arrow to \AgdaSymbol{∀} \AgdaSymbol{\{}\AgdaBound{a} \AgdaBound{m} \AgdaBound{n}\AgdaSymbol{\}} and let Agda infer the types of \AgdaBound{a}, \AgdaBound{m} and \AgdaBound{n}.

Two more ways exist in Agda to declare new types in addition to \AgdaKeyword{data} definitions. Firstly, functions can accept types as arguments and return them too. As an example, we can define the type of three-element vectors like so:

%TC:ignore
\begin{code}
  Triplet : ∀ {a} → (A : Set a) → Set a
  Triplet A = Vec A (suc (suc (suc zero)))
\end{code}
%TC:endignore

\minisec{Record types}

The \AgdaKeyword{record} keyword lets us define product types in a convenient manner. A non-dependent pair type could be defined like this:

%TC:ignore
\begin{code}
  record Pair {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      fst  : A
      snd  : B
\end{code}
%TC:endignore

The level of this type is the least upper bound of \AgdaBound{a} and \AgdaBound{b} to accomodate fields at levels \AgdaBound{a} and \AgdaBound{b}, written as \AgdaBound{a} \AgdaFunction{⊔} \AgdaBound{b}. Giving a \AgdaKeyword{constructor} is optional but necessary for pattern matching. It also makes defining new values less verbose:

%TC:ignore
\begin{code}
  pair₀ pair₁ : Pair ℕ Bool
  pair₁ = record { fst = zero ; snd = false }
  pair₀ = zero , false
\end{code}
%TC:endignore

As a \AgdaKeyword{record} type, \AgdaDatatype{Pair} can be deconstructed in many ways. The name of the type and the name of the field, separated by a dot, can be used to access that field (\AgdaFunction{fst₀}). Alternatively, \AgdaKeyword{open} followed by the name of the type can be used to bring the names of the field accessors into scope (\AgdaFunction{fst₁}). The fields themselves can be brought into scope by \AgdaKeyword{open}ing the type followed by the value whose fields we want to access (\AgdaFunction{fst₂}). Note that \AgdaKeyword{let} … \AgdaKeyword{in} \AgdaBound{x} and \AgdaBound{x} \AgdaKeyword{where} … can be used almost interchangeably. In the last example, we pattern match on the constructor of the type to extract its fields (\AgdaFunction{fst₃}).

%TC:ignore
\begin{code}
  fst₀ fst₁ fst₂ fst₃ : ∀ {a b} → {A : Set a} {B : Set b} → Pair A B → A
  fst₀ = Pair.fst
  fst₁ = let open Pair in fst
  fst₂ p = fst where open Pair p
  fst₃ (fst , snd) = fst
\end{code}
%TC:endignore

\section{Logic and types (will probably be deleted)}

XXX todo:
\begin{itemize}
\item Ignoring universes / levels in this report.
\item Value and \enquote{canonical element} used interchangeably.
\item Alpha-, beta-, eta-conversion. Basics of typed lambda calculus.
\item Truth = type inhabitation, falsity = absurdity
\end{itemize}

In this section, I will briefly review the connection between logic and type theory known as the \enquote{Curry-Howard correspondence}. It lies at the heart of all type theory-based theorem provers.

Fundamentally, to do automated reasoning in a mathematical logic (as opposed to, say, common-sense reasoning), three components are required:

\begin{description}
\item[Propositions and proofs] need to be represented within the system. In typed lambda calculi, propositions are represented as types and lambda terms correspond to proofs.
\item[Deduction rules] must be defined. Typing rules play this role in typed lambda calculi. Logics that can be represented in this way include intuitionistic propositional and predicate logics of various kinds as well as classical logics.
\item[Automation] makes the proof writer's job easier. There are several approaches to automation in different proof assistants based on the Curry-Howard correspondence. Agda, the theorem prover I used in my project, allows for interactive refinement of terms/proofs in a development environment.\footnote{Agda (\url{http://wiki.portal.chalmers.se/agda/pmwiki.php}) uses the proof search tool \emph{Agsy} \autocite{lindblad_tool_2006} to find terms (proofs) in the current scope that have a certain type (prove a given proposition).}
\end{description}

In order to use type theories as theorem provers, \emph{type checking} must be decidable: given a term and a type, the type checker can always tell whether or not the term has this particular type. This translates to \enquote{proposition checking} via the Curry-Howard correspondence: in the logics corresponding to that type theory, we can always decide if a given proof actually proves a certain proposition.

% An advantage of using typed lambda calculi to represent logic is that by stripping away the types, we can easily extract lambda terms that can be executed, giving us verified software for free---this is usually referred to as the \emph{computational fragment} of the typed lambda calculus.

\subsection{Basic notions and notation}

Familiarity with some notions from logic and type theory will be assumed in later sections. To make this report self-contained, I include a brief introduction here.

\minisec{Logic}

Basic notions in logic include propositions, judgements and contexts. Inference rules and tree-shaped formal proofs are commonly used notations.

\begin{description}
\item[Propositions] are generated from the grammar of the logic. For example, in a logic consisting of the constants \(\top\) and \(\bot\) and the logical connectives \(\_\!\!\wedge\!\!\_\) and \(\_\!\!\rightarrow\!\!\_\), we can construct the propositions \(\top \wedge \bot\), \(\bot \rightarrow \bot\), \(\bot \rightarrow ((\bot \wedge \top) \rightarrow \bot)\) and so on. Usually \(A, B, C\) range over propositions.
\item[Contexts] are sets of propositions. \(\Gamma\) and \(\Delta\) are commonly used to denote contexts.
\item[Judgements] have the form \(\Gamma \vdash A\) where \(\Gamma\) is a context and \(A\) is a proposition. The meaning of such a statement is \enquote{if the propositions in \(\Gamma\) hold, then it can be shown that \(A\) holds}.
\end{description}

As an example of an \emph{inference rule}, take the rule that introduces the logical connective \(\_\!\!\wedge\!\!\_\):

\begin{figure}[h]
\begin{prooftree}
    \AxiomC{\(\Gamma \vdash A\)}
    \AxiomC{\(\Delta \vdash B\)}
    \LeftLabel{(\(\wedge\)I)}
    \BinaryInfC{\(\Gamma,\Delta \vdash A \wedge B\)}
\end{prooftree}
\end{figure}

The premisses (zero or more) are written above the line and the conclusion (exactly one) below it. \(\Gamma,\Delta\) is common notation for \(\Gamma \cup \Delta\). Rules without premisses are called \enquote{axioms}. The above rule is meant to be read \enquote{assuming that if all propositions in \(\Gamma\) hold then \(A\) holds and also that if all propositions in \(\Delta\) hold then \(B\) holds, we can conclude that if all propositions in \(\Gamma \cup \Delta\) hold then \(A \wedge B\) holds.}

Rules and axioms are combined into tree-shaped proofs like the one in \cref{fig:example-proof}. Two more notational conventions are used here: an assumption-free judgement \(\{\} \vdash A\) is written \(\vdash A\), and usually the curly braces around the set of assumptions is not written, so one will commonly see \(A,B \vdash C\) instead of \(\{A,B\} \vdash C\).

\begin{figure}[h]
\begin{prooftree}
    \AxiomC{}
    \LeftLabel{\scriptsize{(axiom)}}
    \UnaryInfC{\(B \wedge A \vdash B \wedge A\)}
    \LeftLabel{\scriptsize{(\(\wedge\)E)}}
    \UnaryInfC{\(B \wedge A \vdash A\)}
    \AxiomC{}
    \LeftLabel{\scriptsize{(axiom)}}
    \UnaryInfC{\(B \wedge A \vdash B \wedge A\)}
    \LeftLabel{\scriptsize{(\(\wedge\)E)}}
    \UnaryInfC{\(B \wedge A \vdash B\)}
    \LeftLabel{\scriptsize{(\(\wedge\)I)}}
    \BinaryInfC{\(B \wedge A \vdash A \wedge B\)}
    \LeftLabel{\scriptsize{(\(\rightarrow\)I)}}
    \UnaryInfC{\(\vdash (B \wedge A) \rightarrow (A \wedge B)\)}
    \AxiomC{}
    \LeftLabel{\scriptsize{(axiom)}}
    \UnaryInfC{\(B \vdash B\)}
    \AxiomC{}
    \LeftLabel{\scriptsize{(axiom)}}
    \UnaryInfC{\(A \vdash A\)}
    \LeftLabel{\scriptsize{(\(\wedge\)I)}}
    \BinaryInfC{\(A,B \vdash B \wedge A\)}
    \LeftLabel{\scriptsize{(\(\rightarrow\)E)}}
    \BinaryInfC{\(A,B \vdash A \wedge B\)}
\end{prooftree}
\caption{A roundabout proof. This example is taken from \textcite{wadler_proofs_2000}.}
\label{fig:example-proof}
\end{figure}


\minisec{Type theory}

The typed lambda calculi that will be discussed in this survey all require the following notions:

\begin{description}
\item[Types] can be thought of as collections of objects. Often types are identified with sets, that is, a typing \(x:A\) (\enquote{\(x\) is of type \(A\)}) is equivalent to \(x \in A\) (\enquote{\(x\) is a member of \(A\)}). Basic types like Bool and \(\mathbb{N}\) (natural numbers) together with type constructors like \(\_\!\!\rightarrow\!\!\_\) (for function types) and \(\_\!\!\times\!\!\_\) (for pairs) constitute a grammar of types.
\item[Contexts] are finite partial functions from variables to types, usually written as \(\Gamma = \{x:A,y:B,\dots\}\) where \(\Gamma\) is the name of the context, \(x\) and \(y\) are variables and \(A\) and \(B\) types. In some type theories, order matters---in this case, contexts are ordered lists of (variable, type) tuples.
\item[Judgements] are written \(\Gamma \vdash t:A\) where \(\Gamma\) is a context, \(t\) is a term in the calculus and \(A\) a type. Such a judgement should be read as \enquote{assuming that the variables occurring free in \(t\) have the types that \(\Gamma\) assigns to them, then it can be shown that \(t\) has type \(A\)}.
\end{description}

Typing judgements are the counterpart to inference rules in logic. The rule for introducing pairs is:

\begin{figure}[h]
\begin{prooftree}
    \AxiomC{\(\Gamma \vdash t:A\)}
    \AxiomC{\(\Delta \vdash u:B\)}
    \LeftLabel{(\(\times\)I)}
    \BinaryInfC{\(\Gamma,\Delta \vdash (t, u) : A \times B\)}
\end{prooftree}
\end{figure}

Premiss, conclusion and axiom have the same meaning as in logic. Typing derivations are built up from typing rules and axioms in the same way that proofs are built from the rules and axioms of logic.

\section{Relations, predicates and decidability}

XXX intro blurb

\minisec{Relations}

Usually in mathematics, a relation between two sets is defined as a subset of the cartesian product of the two sets. In a dependent type theory, a binary relation between types \AgdaDatatype{A} \AgdaSymbol{:} \AgdaPrimitiveType{Set} and \AgdaDatatype{B} \AgdaSymbol{:} \AgdaPrimitiveType{Set} has the type \AgdaDatatype{A} \AgdaSymbol{→} \AgdaDatatype{B} \AgdaSymbol{→} \AgdaPrimitiveType{Set}. Via currying, this type is isomorphic to \AgdaDatatype{A} \AgdaDatatype{×} \AgdaDatatype{B} \AgdaSymbol{→} \AgdaPrimitiveType{Set}. A common way to think about this constructive way of defining relations is to view the resulting type as evidence that the two arguments are related.

We will restrict our attention to the special case of relations between inhabitants of the same type, called \emph{homogeneous} relations.

\emph{Divisibility} is a familiar notion with a straightforward definition as a type.

%TC:ignore
\AgdaHide{
\begin{code}
module _ where
  open import Data.Nat.Base
  open import Relation.Binary.PropositionalEquality
\end{code}
}

\begin{code}
  data _∣_ : ℕ → ℕ → Set where
    divides : {m n : ℕ} (q : ℕ) (eq : n ≡ q * m) → m ∣ n

  1-divides-n : ∀ n → 1 ∣ n
  1-divides-n n = divides {1} {n} n n≡n*1
    where
      n≡n*1 : ∀ {n} → n ≡ n * 1
      n≡n*1 {zero}  = refl
      n≡n*1 {suc n} = cong suc n≡n*1
\end{code}
%TC:endignore

Its definition translates to \enquote{\(m\) divides \(n\) if there exists a \(q\) such that \(n \equiv q m\)}.

An important homogeneous binary relation is called \emph{propositional equality}, written as \AgdaDatatype{\_≡\_} in Agda (also called \(I\) in the literature). Two elements of the same type are propositionally equal if they can be shown to reduce to the same value.

%TC:ignore
\AgdaHide{
\begin{code}
module PropEq where
\end{code}
}

\begin{code}
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x
\end{code}
%TC:endignore

The relation \AgdaDatatype{\_≡\_} has only one constructor called \AgdaInductiveConstructor{refl}. In order to create an inhabitant of the propositional equality type, we must use this constructor---there is no other way.

The constructor \AgdaInductiveConstructor{refl} requires that its two arguments have the same value. Therefore, in order to obtain an inhabitant of \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{y}, \AgdaBound{x} and \AgdaBound{y} must be shown to reduce to the same value.

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
  open import Data.Empty
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

\section{Equivalences and setoids}

The main use case of the agda-bigops library is to prove equalities. As an example, the Binomial Theorem can be stated as \[ (1 + x)^n = \sum_{k = 0}^n \binom{n}{k} \; x^k \]

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

\section{Matrices}

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
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)
  open P.≡-Reasoning
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

\section{Differences to big operators in Coq}

\chapter{Square matrices over semirings}

% XXX Things that will have to be explained for this chapter to make sense:
% ∀-notation; open ... using notation; all the lemmas in Bigop.Properties; ℕ and Fin; pattern matching; the Matrix library (representation as Vec of Vecs; tabulate; lookup; syntax); universe levels and ⊔; REL A B ℓ; implicit arguments; records (constructors and fields); how algebraic structures publicly export / import the properties of their substructures; equational reasoning; propositional equality implies any other kind of equivalence via `reflexive`; binary operators and mixfix operators _⊕_ and _[_,_]

Square matrices over semirings are again semirings. Spelling this out in more detail, square matrices of a particular size whose elements belong to the carrier of a semiring together with matrix addition and multiplication defined using the addition and multiplication of the element semiring again form a semiring.

Proving this fact using the library developed in this project was the success criterion set in the project proposal. This chapter describes the proof and how it makes use of the \AgdaModule{Bigop} library.

%TC:ignore
\AgdaHide{
\begin{code}
module SquareMatrixSemiringProof where

  open import Matrix
  open import Bigop

  open import Algebra
  open import Algebra.FunctionProperties
  open import Algebra.Structures
  open import Data.Empty
  open import Data.Fin using (Fin) renaming (zero to zeroF; suc to sucF)
  open import Data.Fin.Properties using (bounded)
  import Data.List.Base as L using ([_])
  import Data.Nat.Base as N
  open N using (ℕ; z≤n)
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

\section{Definitions}

The proof starts by defining an equivalence relation for matrices.\footnote{To be precise, \AgdaDatatype{Pointwise} \AgdaDatatype{\_\sim\_} is just a relation for now. The proof that it really is an equivalence relation provided that \AgdaDatatype{\_\sim\_} is one comes later.} It is defined by pointwise equivalence between the elements of two matrices of the same shape.

%TC:ignore
\begin{code}
  record Pointwise  {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ)
                    {m n} (x : Matrix A m n) (y : Matrix B m n) : Set (a ⊔ b ⊔ ℓ) where
    constructor ext
    field app : (r : Fin m) (c : Fin n) → x [ r , c ] ∼ y [ r , c ]
\end{code}
%TC:endignore

This definition can be read as follows: in order to show that the \AgdaDatatype{Pointwise} \AgdaDatatype{\_\sim\_} relation holds between two matrices, we must give a function which for any row index \AgdaBound{r} and any column index \AgdaBound{c} and returns evidence that the relation \AgdaDatatype{\_\sim\_} holds between the elements of the two matrices at this point.

The remainder of the proof resides in a module that is parameterised over the size \AgdaBound{n} of the matrices and the underlying semiring.

%TC:ignore
\begin{code}
  module SquareMatrix (n : ℕ) {c ℓ} (semiring : Semiring c ℓ) where
\end{code}
%TC:endignore

To begin, we bring the underlying semiring with its carrier type, special elements, operators and substructures into scope. Here \emph{substructures} refers to the weaker structures that can automatically be derived from the a given algebraic structure by subtracting properties, operators or special elements. For example, any commutative monoid gives rise to a monoid if we forget about the commutative law.

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

Next, the equivalence relation \AgdaDatatype{\_≈\_} of the underlying setoid and its reflexive, symmetric and transitive laws (\AgdaField{refl}, \AgdaField{sym}, \AgdaField{trans}) are brought into scope. We make the sum syntax from the \AgdaModule{Bigop.Core.Fold} module available and open the ordinals lemmas, equational reasoning in the element setoid and propositional equality reasoning.

%TC:ignore
\begin{code}
    open Setoid setoid using (_≈_; refl; sym; trans; reflexive)
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

\AgdaDatatype{M} a shortcut for the type of square matrices of size \AgdaBound{n} over the carrier of the underlying semiring.

%TC:ignore
\begin{code}
    M : Set c
    M = Matrix Carrier n n
\end{code}
%TC:endignore

We call the pointwise relation between two square matrices of the same size \AgdaDatatype{\_≋\_}.

%TC:ignore
\begin{code}
    _≋_ : Rel M (c ⊔ ℓ)
    _≋_ = Pointwise _≈_
\end{code}
%TC:endignore

Next, we define matrix addition \AgdaFunction{\_⊕\_} and multiplication \AgdaFunction{\_⊗\_}. Addition works pointwise. \AgdaFunction{tabulate} populates a matrix using a function that takes the row and column index to an element of the matrix by applying that function to each position in the matrix.

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

The matrix \AgdaFunction{0M} is the identity for matrix addition and the annihilator for matrix multiplication. All its elements are set to the zero element of the underlying semiring.

%TC:ignore
\begin{code}
    0M : M
    0M = tabulate (λ r c → 0#)
\end{code}
%TC:endignore

\AgdaFunction{1M} is the identity for matrix multiplication. Its definition relies on the function \AgdaFunction{diag}, which returns \AgdaBound{1\#} if its arguments are equal and \AgdaBound{0\#} if they are different.\footnote{There are many ways to define the function \AgdaFunction{diag}. One alternative would be to use an explicit equality test. I found the inductive definition given above easier to work with in proofs.}

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

This concludes the preliminary definitions.

\section{Auxiliary lemmas}

The next two lemmas show that the elements of the identity matrix \AgdaFunction{1M} are equal to \AgdaFunction{1\#} on the diagonal and \AgdaFunction{0\#} everywhere else.

%TC:ignore
\begin{code}
    1M-diag : ∀ {r c} → r ≡ c → 1M [ r , c ] ≡ 1#
\end{code}
\AgdaHide{
\begin{code}
    1M-diag {r} {.r} P.refl = start
      1M [ r , r ]  ≣⟨ l∘t r r ⟩
      diag r r      ≣⟨ diag-lemma r ⟩
      1#            □
        where
          diag-lemma  : ∀ {n} (r : Fin n) → diag r r ≡ 1#
          diag-lemma  zeroF     =  P.refl
          diag-lemma  (sucF r)  =  diag-lemma r
\end{code}
}
\begin{code}
    1M-∁-diag  : ∀ {r c} → ∁ (_≡_ r) c → 1M [ r , c ] ≡ 0#
    -- Proofs omitted.
\end{code}
\AgdaHide{
\begin{code}
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
}
%TC:endignore

\section{Proofs}


\minisec{\AgdaDatatype{\_≋\_} is an equivalence relation}

For \AgdaDatatype{\_≋\_} to be an equivalence relation, it needs to be reflexive, symmetric and transitive. All three properties follow directly from the fact that the underlying element-wise relation \AgdaDatatype{\_≈\_} is an equivalence.

%TC:ignore
\begin{code}
    ≋-isEquivalence : IsEquivalence _≋_
    ≋-isEquivalence = record { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans }
      where
        ≋-refl : Reflexive _≋_
        ≋-refl = ext (λ r c → refl)

        ≋-sym : Symmetric _≋_
        ≋-sym (ext app) = ext (λ r c → sym (app r c))

        ≋-trans : Transitive _≋_
        ≋-trans (ext app₁) (ext app₂) = ext (λ r c → trans (app₁ r c) (app₂ r c))
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


\minisec{Associativity of matrix addition}

Our first algebraic proof shows that matrix addition is associative, that is, \((A ⊕ B) ⊕ C ≋ A ⊕ (B ⊕ C)\). Since matrix addition is defined as elementwise addition, the proof of elementwise equivalence is straightforward: unfold the definition of \AgdaFunction{\_⊕\_}; use associativity of the elementwise addition \AgdaFunction{\_+\_}; fold back into matrix addition.

The auxiliary functions \AgdaFunction{factorˡ} and \AgdaFunction{factorʳ} simply unfold the nested matrix additions.

%TC:ignore
\begin{code}
    ⊕-assoc : Associative _≋_ _⊕_
    ⊕-assoc A B C = ext assoc
      where
        open Semigroup +-semigroup using () renaming (assoc to +-assoc)

        assoc : ∀ r c → ((A ⊕ B) ⊕ C) [ r , c ] ≈ (A ⊕ (B ⊕ C)) [ r , c ]
        assoc r c = begin
          ((A ⊕ B) ⊕ C) [ r , c ]                     ≡⟨ factorˡ r c ⟩
          (A [ r , c ] +  B [ r , c ]) + C [ r , c ]  ≈⟨ +-assoc _ _ _ ⟩
          A [ r , c ] + (B [ r , c ]  + C [ r , c ])  ≡⟨ P.sym (factorʳ r c) ⟩
          (A ⊕ (B ⊕ C)) [ r , c ]                     ∎
\end{code}
\AgdaHide{
\begin{code}
          where
            factorˡ : ∀ r c → ((A ⊕ B) ⊕ C) [ r , c ] ≡ (A [ r , c ] + B [ r , c ]) + C [ r , c ]
            factorˡ r c = l∘t r c ⟨ P.trans ⟩ P.cong₂ _+_ (l∘t r c) P.refl

            factorʳ : ∀ r c → (A ⊕ (B ⊕ C)) [ r , c ] ≡ A [ r , c ] + (B [ r , c ] + C [ r , c ])
            factorʳ r c = l∘t r c ⟨ P.trans ⟩ P.cong₂ _+_ P.refl (l∘t r c)
\end{code}
}
%TC:endignore

Since the only law used in this proof is \AgdaFunction{+-assoc}, the semigroup over \AgdaFunction{\_+\_} induced by the underlying semiring is sufficient to prove that matrix addition is associative.

\minisec{Congruence of matrix addition}

Usually in mathematical reasoning, we expect that replacing a subterm \(S\) by an equivalent subterm \(S′\) within a term \(T\) gives a term \(T[S′/S]\) that is equivalent to the original term, so \(S ≈ S′ ⇒ T ≈ T[S′/S]\). A special case of this is \(T = f(S)\) for some function \(f\). In a formal system like Agda, the \(f\)-property \(S ≈ S′ ⇒ f(S) ≈ f(S′)\) is called \emph{congruence} or \emph{preservation of equivalence} and must be proved for each function.

Here we prove that matrix addition preserves equivalence, that is, \(A ≋ A′ ∧ B ≋ B′ ⇒ A ⊕ B ≋ A′ ⊕ B′\).

%TC:ignore
\begin{code}
    ⊕-cong : _⊕_ Preserves₂ _≋_ ⟶ _≋_ ⟶ _≋_
    ⊕-cong {A} {A′} {B} {B′} (ext app₁) (ext app₂) = ext cong
      where
        open Semigroup +-semigroup using () renaming (∙-cong to +-cong)

        cong : ∀ r c → (A ⊕ B) [ r , c ] ≈ (A′ ⊕ B′) [ r , c ]
        cong r c = begin
          (A ⊕ B) [ r , c ]             ≡⟨ l∘t r c ⟩
          A [ r , c ]   + B [ r , c ]   ≈⟨ +-cong (app₁ r c) (app₂ r c) ⟩
          A′ [ r , c ]  + B′ [ r , c ]  ≡⟨ P.sym (l∘t r c) ⟩
          (A′ ⊕ B′) [ r , c ]           ∎
\end{code}
%TC:endignore

The structure of the proof is similar to the associativity proof above. Again, a semigroup over \AgdaFunction{\_+\_} provides sufficient structure.

\minisec{Left zero for matrix multiplication}

In this proof that \AgdaFunction{0M} is the left zero for \AgdaFunction{\_⊗\_}, that is, \AgdaFunction{0M} \AgdaFunction{⊗} \AgdaBound{A} \AgdaDatatype{≋} \AgdaFunction{0M}, we use two lemmas from \AgdaModule{Bigop.Properties} for the first time.

As described in XXX, \AgdaFunction{Σ.cong} states that if lists \AgdaBound{is} and \AgdaBound{js} are propositionally equal and functions \AgdaBound{f} and \AgdaBound{g} are extensionally equal with respect to \AgdaDatatype{\_≈\_}, then \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{is} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{j} \AgdaFunction{←} \AgdaBound{js} \AgdaFunction{]} \AgdaBound{g} \AgdaBound{j}.

%TC:ignore
\begin{code}
    M-zeroˡ : LeftZero _≋_ 0M _⊗_
    M-zeroˡ A = ext z
      where
        open SemiringWithoutOne semiringWithoutOne using (*-cong; zero)
        module Σ = Props.SemiringWithoutOne semiringWithoutOne using (cong; distrˡ)

        z : ∀ r c → (0M ⊗ A) [ r , c ] ≈ 0M [ r , c ]
        z r c = begin
          (0M ⊗ A) [ r , c ]                       ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] 0M [ r , i ] * A [ i , c ]  ≈⟨ Σ.cong  (ι n) P.refl
                                                              (λ i → reflexive (l∘t r i) ⟨ *-cong ⟩ refl) ⟩
          Σ[ i ← ι n ] 0# * A [ i , c ]            ≈⟨ sym (Σ.distrˡ _ 0# (ι n)) ⟩
          0# * (Σ[ i ← ι n ] A [ i , c ])          ≈⟨ proj₁ zero _ ⟩
          0#                                       ≡⟨ P.sym (l∘t r c) ⟩
          0M [ r , c ]                             ∎
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
    ⊗-assoc A B C = ext assoc
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

        assoc : ∀ r c → ((A ⊗ B) ⊗ C) [ r , c ] ≈ (A ⊗ (B ⊗ C)) [ r , c ]
        assoc r c = begin
{- 3.1 -}  ((A ⊗ B) ⊗ C) [ r , c ]                                              ≈⟨ factorˡ r c ⟩
{- 3.2 -}  Σ[ i ← ι n ] (Σ[ j ← ι n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]  ≈⟨ Σ.cong (ι n) P.refl (λ i → Σ.distrʳ _ _ (ι n)) ⟩
{- 3.3 -}  Σ[ i ← ι n ] Σ[ j ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]  ≈⟨ Σ.swap _ (ι n) (ι n) ⟩
           Σ[ j ← ι n ] Σ[ i ← ι n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]  ≈⟨ Σ.cong (ι n) P.refl (inner r c) ⟩
{- 3.6 -}  Σ[ j ← ι n ] A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ])  ≈⟨ sym $ factorʳ r c ⟩
          (A ⊗ (B ⊗ C)) [ r , c ]                                               ∎
\end{code}
\AgdaHide{
\begin{code}
          where
            factorˡ : ∀ r c →
                      ((A ⊗ B) ⊗ C) [ r , c ] ≈
                      Σ[ i ← ι n ] (Σ[ j ← ι n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]
            factorˡ r c = reflexive (l∘t r c) ⟨ trans ⟩
                          Σ.cong (ι n) P.refl (λ i → *-cong (reflexive (l∘t r i)) refl)

            factorʳ : ∀ r c →
                      (A ⊗ (B ⊗ C)) [ r , c ] ≈
                      Σ[ j ← ι n ] A [ r , j ] * (Σ[ i ← ι n ] B [ j , i ] * C [ i , c ])
            factorʳ r c = reflexive (l∘t r c) ⟨ trans ⟩
                          Σ.cong (ι n) P.refl (λ j → *-cong refl (reflexive (l∘t j c)))
\end{code}
}
%TC:endignore


\minisec{Left-distributivity}

This proof shows that \AgdaBound{A} \AgdaFunction{⊗} \AgdaSymbol{(}\AgdaBound{B} \AgdaFunction{⊕} \AgdaBound{C}\AgdaSymbol{)} \AgdaDatatype{≋} \AgdaSymbol{(}\AgdaBound{A} \AgdaFunction{⊗} \AgdaBound{B}\AgdaSymbol{)} \AgdaFunction{⊕} \AgdaSymbol{(}\AgdaBound{A} \AgdaFunction{⊗} \AgdaBound{C}\AgdaSymbol{)}. Most of \AgdaFunction{distr} is concerned with unfolding the definition of \AgdaFunction{\_⊕\_} and \AgdaFunction{\_⊗\_}. The crucial step in the proof is the application of the left-distributivity law of the underlying semiring in \AgdaFunction{inner} (1) followed by the use of \AgdaFunction{Σ.merge} in \AgdaFunction{distr} (2), splitting the sum into two.

%TC:ignore
\begin{code}
    ⊗-distrOverˡ-⊕ : (_≋_ DistributesOverˡ _⊗_) _⊕_
    ⊗-distrOverˡ-⊕ A B C = ext distr
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


\minisec{Left identity for matrix multiplication}

This is the longest of the semiring proofs. We show that \AgdaFunction{1M} \AgdaFunction{⊗} \AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{A} for all \AgdaBound{A}. The key idea here is that for any term involving \AgdaFunction{1M}, it makes sense to case split on whether the row \AgdaBound{r} and column \AgdaBound{c} are equal. If they are, then \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{1\#} by \AgdaFunction{1M-diag}. If not, then by \AgdaFunction{1M-∁-diag} we have \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{0\#}.

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
    ⊗-identityˡ A = ext ident
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

        ident : ∀ r c → (1M ⊗ A) [ r , c ] ≈ A [ r , c ]
        ident r c = begin
          (1M ⊗ A) [ r , c ]                                     ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] 1M [ r , i ] * A [ i , c ]                ≈⟨ Σ.split-P _ (ι n) (≟ r) ⟩
          Σ[ i ← ι n ∥ ≟ r ]       1M [ r , i ] * A [ i , c ] +
          Σ[ i ← ι n ∥ ∁′ (≟ r) ]  1M [ r , i ] * A [ i , c ]    ≈⟨ ≡-step r c ⟨ +-cong ⟩ ≢-step r c ⟩
          Σ[ i ← ι n ∥ ≟ r ] A [ i , c ] + 0#                    ≈⟨ proj₂ +-identity _ ⟩
          Σ[ i ← ι n ∥ ≟ r ] A [ i , c ]                         ≡⟨ P.cong  (Σ-syntax (λ i → A [ i , c ]))
                                                                            (filter r c) ⟩
          A [ r , c ] + 0#                                       ≈⟨ proj₂ +-identity _  ⟩
          A [ r , c ]                                            ∎
\end{code}
%TC:endignore

\chapter{Evaluation}

\section{Theorems proved}

Binomial theorem

Gauss

\printbibliography

\end{document}
