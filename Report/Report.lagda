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
  import Data.Vec as V using (lookup; tabulate)
  open import Data.Vec.Properties using (lookup∘tabulate)
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
%TC:endignore

\section{Definitions}

The proof starts by defining an equivalence relation for matrices.\footnote{To be precise, \AgdaDatatype{Pointwise} \AgdaDatatype{\_\sim\_} is just a relation for now. The proof that it really is an equivalence relation provided that \AgdaDatatype{\_\sim\_} is one comes later.} It is defined by pointwise equivalence between the elements of two matrices of the same shape.

%TC:ignore
\begin{code}
  record Pointwise {a b ℓ} {A : Set a} {B : Set b} (_∼_ : REL A B ℓ)
                   {m n} (x : Matrix A m n) (y : Matrix B m n) : Set (a ⊔ b ⊔ ℓ) where
    constructor ext
    field app : (r : Fin m) (c : Fin n) → x [ r , c ] ∼ y [ r , c ]
\end{code}
%TC:endignore

This definition can be read as follows: in order to show that the \AgdaDatatype{Pointwise} relation holds between two matrices, we must give a function which for any row index \AgdaBound{r} and any column index \AgdaBound{c} and returns evidence that the relation \AgdaDatatype{\_\sim\_} holds between the elements of the two matrices at this point.

The remainder of the proof resides in a module that is parameterised over the size \AgdaBound{n} of the matrices and the underlying semiring.

%TC:ignore
\begin{code}
  module SquareMatrix (n : ℕ) {c ℓ} (semiring : Semiring c ℓ) where
\end{code}
%TC:endignore

To begin, we bring the underlying semiring with its special elements, operators, induced substructures and carrier type into scope. \emph{Induced substructures} are the weaker structures that can automatically be derived from the given structure by subtracting properties, operators or special elements. For example, any commutative monoid gives rise to a monoid if we forget about the commutative law.

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
      using ()
      renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)
\end{code}

\AgdaHide{
\begin{code}
    ι = fromLenF 0
\end{code}
}
%TC:endignore

\AgdaDatatype{M} \AgdaBound{n} is defined as a shortcut for the type of square matrices of size \AgdaBound{n} over the carrier of the underlying semiring.

%TC:ignore
\begin{code}
    M : ℕ → Set c
    M n = Matrix Carrier n n
\end{code}
%TC:endignore

We call the pointwise relation between two square matrices of the same size \AgdaDatatype{\_≋\_}.

%TC:ignore
\begin{code}
    _≋_ : Rel (M n) (c ⊔ ℓ)
    _≋_ = Pointwise _≈_
\end{code}
%TC:endignore

We are now ready to define matrix addition \AgdaFunction{\_⊕\_} and multiplication \AgdaFunction{\_⊗\_}. Addition works pointwise. \AgdaFunction{tabulate} populates a matrix using a function that takes the row and column index to an element of the matrix by applying that function to each position in the matrix.

%TC:ignore
\begin{code}
    _⊕_ : Op₂ (M n)
    A ⊕ B = tabulate (λ r c → A [ r , c ] + B [ r , c ])
\end{code}
%TC:endignore

Using Σ-syntax, multiplication can be defined in a concise way.

%TC:ignore
\begin{code}
    mult : M n → M n → Fin n → Fin n → Carrier
    mult A B r c = Σ[ i ← ι n ] A [ r , i ] * B [ i , c ]

    _⊗_ : Op₂ (M n)
    A ⊗ B = tabulate (mult A B)
\end{code}
%TC:endignore

Note how the definition of \AgdaFunction{mult} resembles the component-wise definition of matrix multiplication in standard mathematical notation, \[(A\,B)_{r,c} = \sum_{i \leftarrow \iota\ n} A_{r,i}\,B_{i,c}\]

The matrix \AgdaFunction{0M} is the identity for matrix addition and the annihilator for matrix multiplication. All its elements are set to the zero element of the underlying semiring.

%TC:ignore
\begin{code}
    0M : M n
    0M = tabulate (λ r c → 0#)
\end{code}
%TC:endignore

\AgdaFunction{1M} is the identity for matrix multiplication. Its definition relies on the function \AgdaFunction{diag}, which returns \AgdaBound{1\#} if its arguments are equal and \AgdaBound{0\#} if they are different.\footnote{There are many ways to define the function \AgdaFunction{diag}. One alternative would be to use an explicit equality test. I found the inductive definition given above easier to work with in proofs.}

%TC:ignore
\begin{code}
    diag : {n : ℕ} → Fin n → Fin n → Carrier
    diag  zeroF     zeroF     =  1#
    diag  zeroF     (sucF c)  =  0#
    diag  (sucF r)  zeroF     =  0#
    diag  (sucF r)  (sucF c)  =  diag r c

    1M : M n
    1M = tabulate diag
\end{code}
%TC:endignore

This concludes the preliminary definitions.

\section{Auxiliary lemmas}

One of the most important lemmas in this file, \AgdaFunction{l∘t}, shows that if a matrix was created by tabulating a function \AgdaBound{f}, then looking up the element at row \AgdaBound{r} and column \AgdaBound{c} returns \AgdaBound{f} \AgdaBound{r} \AgdaBound{c}. The proof uses a similar lemma for vectors, \AgdaFunction{lookup∘tabulate}.

%TC:ignore
\begin{code}
    l∘t : ∀ {f : Fin n → Fin n → Carrier} r c → lookup r c (tabulate f) ≡ f r c
    -- Proof omitted.
\end{code}
\AgdaHide{
\begin{code}
    l∘t {f} r c = P.trans  (P.cong  (V.lookup c)
                                    (lookup∘tabulate (λ r → V.tabulate (f r)) r))
                           (lookup∘tabulate (f r) c)
\end{code}
}
%TC:endignore

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

XXX not sure if ≋-isEquivalence should be discussed.

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

\minisec{Associativity of matrix addition}

The first algebraic proof shows that matrix addition is associative, that is, \((A ⊕ B) ⊕ C ≋ A ⊕ (B ⊕ C)\). Since matrix addition is defined as elementwise addition, the proof of elementwise equivalence is straightforward: unfold the definition of \AgdaFunction{\_⊕\_}; use associativity of the elementwise addition \AgdaFunction{\_+\_}; fold back into matrix addition.

Auxiliary functions \AgdaFunction{factorˡ} and \AgdaFunction{factorʳ} take care of the bookkeeping.

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

Usually in mathematical reasoning, we expect that replacing a subterm \(S\) by an equivalent subterm \(S′\) within a term \(T\) gives a term \(T[S′/S]\) that is equivalent to the original term, so \(S ≈ S′ ⇒ T ≈ T[S′/S]\). A special case of this is \(T = f(S)\) for some function \(f\). In a formal system like Agda, the \(f\)-property \(S ≈ S′ ⇒ f(S) ≈ f(S′)\) is called \emph{preservation of equivalence} or \emph{congruence} and must be proved for each function.

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

Again, we use the appropriate congruence rules to replace equals by equals within terms. Steps (3.4) and (3.5) have been factored into a separate function \AgdaFunction{inner} to make the proof more readable.

%TC:ignore
\begin{code}
    ⊗-assoc : Associative _≋_ _⊗_
    ⊗-assoc A B C = ext assoc
      where
        open SemiringWithoutOne semiringWithoutOne using (*-assoc; *-cong)
        module Σ = Props.SemiringWithoutOne semiringWithoutOne using (cong; swap; distrˡ; distrʳ)

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

\minisec{Left identity for matrix multiplication}

This is the longest of the semiring proofs. We show that \AgdaFunction{1M} \AgdaFunction{⊗} \AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{A} for all \AgdaBound{A}. The key idea here is that for any term involving \AgdaFunction{1M}, it makes sense to case split on whether the row \AgdaBound{r} and column \AgdaBound{c} are equal. If they are, then \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{1\#} by \AgdaFunction{1M-diag}. If not, then by \AgdaFunction{1M-∁-diag} we have \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{0\#}.

In \AgdaFunction{ident}, after unfolding the definition of \AgdaFunction{⊗}, we split the list (\AgdaFunction{ι} \AgdaBound{n}) that is being summed over by the decidable predicate (\AgdaFunction{≟} \AgdaBound{r}) using \AgdaFunction{Σ.split-P}. This lets us consider the cases \AgdaBound{r} \AgdaFunction{≈} \AgdaBound{i} and \AgdaBound{r} \AgdaFunction{≉} \AgdaBound{i} separately.

\AgdaFunction{≈-step} deals with the first case. From \AgdaBound{r} \AgdaFunction{≈} \AgdaBound{i} follows \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{1\#}. Using distributivity and the identity law for \AgdaFunction{\_*\_}, we can deduce that

\[ \text{
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaFunction{ι} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{≟} \AgdaBound{r} \AgdaFunction{]} \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaFunction{≈}
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaFunction{ι} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{≟} \AgdaBound{r} \AgdaFunction{]} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}
}\]

Otherwise, \AgdaFunction{≉-step} assumes that \AgdaBound{r} \AgdaFunction{≉} \AgdaBound{i}. It follows that \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{0\#}. Then by distributivity and the \AgdaFunction{zero} law of the underlying semiring, it follows that

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

        p-step :  ∀ r c →
                  Σ[ i ← ι n ∥ (_≟F_ r) ] 1M [ r , i ] * A [ i , c ] ≈
                  Σ[ i ← ι n ∥ (_≟F_ r) ] A [ i , c ]
        p-step r c = begin
          Σ[ i ← ι n ∥ (_≟F_ r) ] 1M [ r , i ] * A [ i , c ]
            ≈⟨ Σ.cong-P  (ι n) (_≟F_ r)
                         (λ i r≡i → reflexive (1M-diag r i r≡i) ⟨ *-cong ⟩ refl) ⟩
          Σ[ i ← ι n ∥ (_≟F_ r) ] 1# * A [ i , c ]    ≈⟨ sym $ Σ.distrˡ _ 1# (ι n ∥ (_≟F_ r)) ⟩
          1# * (Σ[ i ← ι n ∥ (_≟F_ r) ] A [ i , c ])  ≈⟨ proj₁ *-identity _ ⟩
          Σ[ i ← ι n ∥ (_≟F_ r) ] A [ i , c ]         ∎

        ¬p-step :  ∀ r c →
                   Σ[ i ← ι n ∥ ∁-dec (_≟F_ r) ] 1M [ r , i ] * A [ i , c ] ≈ 0#
        ¬p-step r c = begin
          Σ[ i ← ι n ∥ ∁-dec (_≟F_ r) ] 1M [ r , i ] * A [ i , c ]
            ≈⟨ Σ.cong-P  (ι n) (∁-dec (_≟F_ r))
                         (λ i r≢i → reflexive (1M-∁-diag r i r≢i) ⟨ *-cong ⟩ refl) ⟩
          Σ[ i ← ι n ∥ ∁-dec (_≟F_ r) ] 0# * A [ i , c ]      ≈⟨ sym $ Σ.distrˡ _ 0# (ι n ∥ ∁-dec (_≟F_ r)) ⟩
          0# * (Σ[ i ← ι n ∥ (∁-dec (_≟F_ r)) ] A [ i , c ])  ≈⟨ proj₁ zero _ ⟩
          0#                                                 ∎

        ident : ∀ r c → (1M ⊗ A) [ r , c ] ≈ A [ r , c ]
        ident r c = begin
          (1M ⊗ A) [ r , c ]                                           ≡⟨ l∘t r c ⟩
          Σ[ i ← ι n ] 1M [ r , i ] * A [ i , c ]                      ≈⟨ Σ.split-P _ (ι n) (_≟F_ r) ⟩
          Σ[ i ← ι n ∥ (_≟F_ r) ]        1M [ r , i ] * A [ i , c ] +
          Σ[ i ← ι n ∥ ∁-dec (_≟F_ r) ]  1M [ r , i ] * A [ i , c ]    ≈⟨ p-step r c ⟨ +-cong ⟩ ¬p-step r c ⟩
          (Σ[ i ← ι n ∥ (_≟F_ r) ] A [ i , c ] + 0#)                   ≈⟨ proj₂ +-identity _ ⟩
          Σ[ i ← ι n ∥ (_≟F_ r) ] A [ i , c ]
            ≡⟨ P.cong  (Σ-syntax (λ i → A [ i , c ]))
                       (ordinals-filterF z≤n (bounded r)) ⟩
          Σ[ i ← L.[ r ] ] A [ i , c ]                                 ≈⟨ proj₂ +-identity _  ⟩
          A [ r , c ]                                                  ∎
\end{code}
%TC:endignore

\chapter{Evaluation}

\section{Theorems proved}

Binomial theorem

Gauss

\printbibliography

\end{document}
