\nonstopmode
% \RequirePackage[l2tabu, orthodox]{nag}
\documentclass[12pt,chapterprefix=true,toc=bibliography,numbers=noendperiod,
               footnotes=multiple,twoside]{scrreprt}

% type-set with agda --latex
\newcommand{\AGDALATEX}[1]{#1}
\newcommand{\PLAINLATEX}[1]{}

\usepackage{mathtools}
\usepackage{unicode-math}
\usepackage{polyglossia}
\setmainlanguage[variant=british]{english}
\usepackage{fontspec}
\setmainfont{TeX Gyre Pagella}
\setsansfont{TeX Gyre Pagella}
\setmathfont{XITS Math}

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
\DeclareUnicodeCharacter{8759}{::}
\DeclareUnicodeCharacter{9733}{$\star$}
\DeclareUnicodeCharacter{8718}{$\blacksquare$}
\DeclareUnicodeCharacter{10214}{$\llbracket$}
\DeclareUnicodeCharacter{10215}{$\rrbracket$}
\DeclareUnicodeCharacter{10218}{$\langle\!\langle$}
\DeclareUnicodeCharacter{10219}{$\rangle\!\rangle$}

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

\begin{titlepage}
\maketitle
\end{titlepage}

\AgdaHide{
\begin{code}
module Report where
\end{code}
}

\chapter{Introduction}

\section{Motivation}

\section{Logic and types}

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

Its definition translates to \enquote{\(m\) divides \(n\) if there exists a \(q\) such that \(n \equiv q m\)}.

An important homogeneous binary relation is called \emph{propositional equality}, written as \AgdaDatatype{\_≡\_} in Agda (also called \(I\) in the literature). Two elements of the same type are propositionally equal if they can be shown to reduce to the same value.

\AgdaHide{
\begin{code}
module PropEq where
\end{code}
}

\begin{code}
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x
\end{code}

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

\begin{align*}
\bigodot_{i \leftarrow \textit{Idx}} \left(f(i) \odot g(i)\right)
&\equiv
\left(\bigodot_{i \leftarrow \textit{Idx}} f(i) \right) \odot \left(\bigodot_{i \leftarrow \textit{Idx}} g(i)\right) \\
\bigodot_{i \leftarrow \textit{Idx}_0} \left(\bigodot_{j \leftarrow \textit{Idx}_1} f(i,j)\right)
&\equiv
\bigodot_{j \leftarrow \textit{Idx}_1} \left(\bigodot_{i \leftarrow \textit{Idx}_0} f(i,j)\right)
\end{align*}

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

\section{Ordinals}

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

\section{Differences to big operators in Coq}

\chapter{Square matrices over semirings}

Square matrices of a particular size whose elements belong to the carrier of a semiring together with matrix addition and multiplication defined using the addition and multiplication of the element semiring again form a semiring.

Proving this fact using the library developed in this project was the success criterion set in the project proposal. This chapter describes the proof and how it makes use of the \AgdaModule{Bigop} library.

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
\end{code}
}

\section{Definitions}

The proof starts by defining an equivalence relation for matrices.\footnote{To be precise, \AgdaDatatype{Pointwise} \AgdaDatatype{\_\sim\_} is just a relation for now. The proof that it really is an equivalence relation provided that \AgdaDatatype{\_\sim\_} is one comes later.} It is defined by pointwise equivalence between the elements of two matrices of the same shape.

\begin{code}
  record Pointwise {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ)
                   {m n} (x : Matrix A m n) (y : Matrix B m n) : Set (a ⊔ b ⊔ ℓ) where
    constructor ext
    field app : (r : Fin m) (c : Fin n) → x [ r , c ] ∼ y [ r , c ]
\end{code}

This definition can be read as follows: in order to show that the \AgdaDatatype{Pointwise} relation holds between two matrices, we must give a function which for any row index \AgdaBound{r} and any column index \AgdaBound{c} and returns evidence that the relation \AgdaDatatype{\_\sim\_} holds between the elements of the two matrices at this point.

The remainder of the proof resides in a module that is parameterised over the size \AgdaBound{n} of the matrices and the underlying semiring.

\begin{code}
  module SquareMatrix (n : ℕ) {c ℓ} (semiring : Semiring c ℓ) where
\end{code}

To begin, we bring the underlying semiring with its special elements, operators, induced substructures and carrier type into scope. \emph{Induced substructures} are the weaker structures that can automatically be derived from the given structure by subtracting properties, operators or special elements. For example, any commutative monoid gives rise to a monoid if we forget about the commutative law.

Semirings contain many induced substructures. In the following, the ones we are interested in are brought into scope explicitly: the commutative monoid, monoid and semigroup over \AgdaFunction{\_+\_}; the monoid and semigroup over \AgdaFunction{\_*\_}; and the \enquote{semiring without one} (a semiring-like structure without an identity for \AgdaFunction{\_*\_}).

\begin{code}
    open Semiring semiring
      using     ( 0#; 1#; _+_; _*_
                ; setoid
                ; +-semigroup; +-monoid; +-commutativeMonoid
                ; *-semigroup; *-monoid; semiringWithoutOne)
      renaming  ( Carrier to A)
\end{code}

Next, the equivalence relation \AgdaDatatype{\_≈\_} of the underlying setoid and its reflexive, symmetric and transitive laws (\AgdaField{refl}, \AgdaField{sym}, \AgdaField{trans}) are brought into scope. We make the sum syntax from the \AgdaModule{Bigop.Core.Fold} module available and open the ordinals lemmas, equational reasoning in the element setoid and propositional equality reasoning.

\begin{code}
    open Setoid setoid using (_≈_; refl; sym; reflexive)
    open Fold +-monoid using (Σ-syntax)
    open Props.Ordinals

    open import Relation.Binary.EqReasoning setoid
    open P.≡-Reasoning
      using ()
      renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)
\end{code}

\AgdaHide{
\begin{code}
    ι = fromLenF 0
\end{code}
}

\AgdaDatatype{M} \AgdaBound{n} is defined as a shortcut for the type of square matrices of size \AgdaBound{n} over the carrier of the underlying semiring.

\begin{code}
    M : ℕ → Set _
    M n = Matrix A n n
\end{code}

We call the pointwise relation between two square matrices of the same size \AgdaDatatype{\_≈M\_}.

\begin{code}
    _≈M_ : Rel (M n) (c ⊔ ℓ)
    _≈M_ = Pointwise _≈_
\end{code}

We are now ready to define matrix addition \AgdaFunction{\_+M\_} and multiplication \AgdaFunction{\_*M\_}. Addition works pointwise. \AgdaFunction{tabulate} populates a matrix using a function that takes the row and column index to an element of the matrix by applying that function to each position in the matrix.

\begin{code}
    _+M_ : Op₂ (M n)
    x +M y = tabulate (λ r c → x [ r , c ] + y [ r , c ])
\end{code}

Using Σ-syntax, multiplication can be defined in a concise way.

\begin{code}
    mult : M n → M n → Fin n → Fin n → A
    mult x y r c = Σ[ i ← ι n ] x [ r , i ] * y [ i , c ]

    _*M_ : Op₂ (M n)
    x *M y = tabulate (mult x y)

    0M : M n
    0M = tabulate (λ r c → 0#)

    diag : {n : ℕ} → Fin n → Fin n → A
    diag zeroF    zeroF    = 1#
    diag zeroF    (sucF c) = 0#
    diag (sucF r) zeroF    = 0#
    diag (sucF r) (sucF c) = diag r c

    1M : M n
    1M = tabulate diag
\end{code}

\chapter{Evaluation}

\section{Theorems proved}

Binomial theorem

Gauss

\printbibliography

\end{document}
