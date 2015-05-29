%TC:newcounter fwords Words in footnotes
%TC:macro \footnote [fwords]

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

\usepackage{pdfpages}
\usepackage{tikz, tikz-qtree}
\usepackage{microtype}
\usepackage{tabularx}
\usepackage{booktabs}
\usepackage{verbatim}
\usepackage{bussproofs}
\usepackage{subcaption}
\usepackage{csquotes}
\usepackage[autocite=inline,citestyle=authoryear-comp,bibstyle=authoryear,
            dashed=false,isbn=false,doi=false,backend=biber,
            date=iso8601,url=false]{biblatex}
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
\newunicodechar{⋀}{\ensuremath{⋀}}
\newunicodechar{⋃}{\ensuremath{⋃}}
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
\urlstyle{tt} % normal text font (alternatives: tt, rm, sf)
\pagestyle{headings}
\addtokomafont{pagehead}{\itshape}

\begin{document}
\setmathfont{Asana-Math.otf}

\includepdf{Cover.pdf}

\pagenumbering{roman}

%TC:ignore
\chapter*{Proforma}
\label{ch:proforma}

\begin{center}
{\renewcommand{\arraystretch}{1.5}%
\begin{tabularx}{419pt}{rX}
\textbf{Name and College} & Leonhard Markert, Emmanuel College \\
\textbf{Project Title} & Big operators in Agda \\
\textbf{Examination} & Computer Science Tripos, Part \textsc{iii} (June 2015) \\
\textbf{Word Count} & XXX words \\
\textbf{Project Originators} & Timothy Griffin, Dominic Mulligan and Leonhard Markert \\
\textbf{Project Supervisors} & Timothy Griffin and Dominic Mulligan
\end{tabularx}}
\end{center}

\section*{Declaration of Originality}
\label{sc:declaration-of-originality}

I, Leonhard Markert of Emmanuel College, being a candidate for Part~\textsc{iii} of the Computer Science Tripos, hereby declare that this dissertation and the work described in it are my own work, unaided except as may be specified below, and that the dissertation does not contain material that has already been used to any substantial extent for a comparable purpose.

\vspace{0.3in}
Signed

\vspace{0.2in}
Date \hspace{0.4in} \today

\section*{Abstract}
\label{sc:original-aims}

We present a library for expressing and proving conjectures involving \enquote{big operators} like \(\sum_{i=0}^n f(i)\) in Agda. We argue that the essence of any such operation is encapsulated in a monoid, an algebraic structure with an identity and associativity law.

In addition to big operators, we formalise intervals of natural numbers, filters and matrices. To demonstrate the definitions and lemmas included in our library, we prove two variants of the Gauss formula as well as the Binomial Theorem and the theorem \enquote{square matrices over a semiring form a semiring}.

\newpage
\tableofcontents
%TC:endignore

\chapter{Introduction\label{ch:Intro}}

%TC:ignore
\AgdaHide{
\begin{code}
module Report where
\end{code}
%TC:endignore
}

\pagenumbering{arabic}

\section{Aims and contributions}

%The \enquote{big sum} operator \(\sum\) (Sigma) is commonly used in various areas of mathematics.\footnote{Chapter 2 of \textcite{graham_concrete_1994}, which is entirely devoted to sums written using Sigma-notation, starts with the words \enquote{SUMS ARE EVERYWHERE in mathematics} (original capitalisation).} Similar big operator notations exist for multiplication \(\Pi\) (Pi), unions \(\bigcup\), least upper bounds \(\bigsqcup\) and so on.

\enquote{SUMS ARE EVERYWHERE}, so begins Chapter 2 of \emph{Concrete mathematics: a foundation for computer science} \autocite{graham_concrete_1994}. Its authors are referring to sums written in Sigma-notation, such as \[\sum_{i ∈ \{1,2,3\}} i² = 1² + 2² +3³\]
\emph{Big operators} generalise this notation to an iteration over any operator with sufficient structure (see \cref{sc:Impl-Bigops}) like multiplication, logical conjunction, set union, max, and so on \autocite{bertot_canonical_2008}.

Proof assistants like \emph{Isabelle} \autocite{paulson_isabelle:_1994}, \emph{Coq} \autocite{huet_coq_2015}, or \emph{Agda} \autocite{norell_dependently_2009} simplify the development of formal proofs. Providing a notation for big operators in a proof assistant is an obvious way to extend the number of proofs that can be expressed naturally. Isabelle and Coq both have libraries that contain syntax definitions and lemmas for dealing with big operators.

No such library currently exists for Agda. The aim of this project was to implement a set of syntax definitions and lemmas that allow users of Agda to write proofs that involve big operators in a notation familiar from handwritten or typeset mathematics.

The main contributions of this project are:

\begin{itemize}
\item Modular syntax for writing sums and other big operators, intervals of natural numbers and filters in Agda that mimicks standard mathematical notation (see \crefrange{sc:Impl-Bigops}{sc:Impl-Filters}).
\item A formalisation of matrices in Agda.
\item Lemmas about big operators based on their underlying algebraic structure (see \cref{sc:Impl-Bigop-Props}).
\item A formal proof of two identities attributed to Gauss (see \cref{ch:Gauss}), the Binomial theorem (see \cref{ch:Binom}) and the theorem \enquote{square matrices over a semiring again form a semiring} (see \cref{ch:Semi}) in Agda.
\end{itemize}

The Agda code and module structure of the implementation follows the same conventions as the standard library.\footnote{An overview of the standard library as a clickable source code file is presented here: \url{https://agda.github.io/agda-stdlib/README.html}} We took care not to duplicate work and instead used definitions from the standard library wherever possible.

%We argue that the essence of any big operator over a possibly-empty collection of indices is a mapping from an index list into the carrier of a monoid followed by a fold over the list of carrier elements using the monoid's binary operator (see \cref{sc:Impl-Bigops}).

\section{Conventions and nomenclature\label{sc:Conventions}}

We need to get two things out of the way before getting into the report: a definition of what exactly constitutes \enquote{big operator}, and what the colours in the Agda code listings stand for.

\minisec{Big operators}

For the purposes of this report, a \emph{big operator} is defined by

\begin{itemize}
\item an \emph{underlying structure} at least containing a \emph{carrier} set (or type), a binary operator \(\_\!\!⊕\!\!\_\) and an element of the carrier, \(ε\);
\item a list of indices \textit{is}; and
\item a function \(f\) from the set (or type) of indices into the carrier.
\end{itemize}
The reasons for choosing this particular representation are discussed in \cref{sc:Impl-Bigops}. We will write the big operator corresponding to the structure described above as \[ \bigoplus_{i ← \textit{is}} f(i) \] Here \(i ← \textit{is}\) indicates that \(i\) ranges over \textit{is}, the list of indices.

\minisec{Code listings}

This report contains Agda code listings. Syntax highlighting is used to make them easier to read. \Cref{tb:Colours} lists the different syntactic categories and how they are typeset in this report.%
\footnote{This report is a \emph{literal Agda file}: every piece of code that is displayed in a grey code box is type checked. Some import statements and definitions are not displayed in the output document for brevity.}

\begin{table}[h]
\centering
\begin{tabular}{l l}
%\toprule
\emph{Notation} & \emph{Role} \\
\midrule
\AgdaInductiveConstructor{refl}\quad \AgdaInductiveConstructor{[]}\quad \AgdaInductiveConstructor{\_∷\_} & Datatype constructors \\
\AgdaDatatype{List}\quad \AgdaDatatype{\_≡\_}\quad \AgdaDatatype{Pred} & Datatype names \\
\AgdaFunction{fold}\quad \AgdaFunction{*-comm}\quad \AgdaFunction{∙-cong} & Functions \\
\AgdaBound{x}\quad \AgdaBound{ys}\quad \AgdaBound{A}\quad \AgdaBound{f} & Bound variables \\
  \AgdaKeyword{open}\quad \AgdaKeyword{with}\quad \AgdaKeyword{where} & Reserved keywords \\
\bottomrule
\end{tabular}
\caption{Colours used in Agda code listings.}
\label{tb:Colours}
\end{table}

\newpage

\section{Motivation\label{sc:Motivation}}

\Textcite{dynerowicz_forwarding_2013} presents an algebraic approach to path problems such as computing the shortest path from one vertex to another in a weighted graph. Each path problem is modelled as a semiring, and its solution is calculated by repeatedly multiplying a matrix representing the weighted graph with itself. We realised that a lot of the infrastructure required to write proofs about shortest-path algorithms does not yet exist in Agda. One critical dependency of such a formalisation effort is a big operator module, which would also be useful in a large range of other contexts.

In this section, we describe how Agda users can write proofs in a style similar to handwritten or typeset ones, assisted by a theorem prover that is integrated into the editing mode for Agda. We then give an example of a proposition that can be expressed and proved using our library, and how it fits naturally into this model of proof development.

\minisec{Agda, Coq and Isabelle}

The current implementation of Agda is relatively new: its foundations were laid in Ulf Norell's doctoral thesis, which was published only in 2007 \autocite{norell_towards_2007}.\footnote{\textcite{coquand_structured_1999} first presented a programming language called Agda. The implementation of the current version of the language was rewritten from scratch. It shares its name and philosophy with the original implementation, but should for all intents and purposes be considered a new language.} In comparison, Lawrence Paulson's work on Isabelle goes back to the late 1980s \autocite{paulson_foundation_1989}, and the earliest Coq user's guide that is available from the archives of the Institut national de recherche en informatique et en automatique (INRIA), the research institute where it was designed and implemented, was published in 1991 \autocite{dowek_coq_1991}.

Partly as a consequence of its young age, Agda's standard library is much smaller than those of Coq and Isabelle. We compare the number of lines of code of the three proof assistants' standard libraries or their equivalents in \cref{tb:Size} as a rough indicator of maturity.\footnote{For Isabelle, the closest equivalent to a standard library is the Higher-Order Logic (HOL) package. The Coq distribution contains a folder \texttt{theories}, which we took as Coq's standard library in the comparison.}

\begin{table}[h]
\centering
\begin{tabular}{l l l l}
%\toprule
\emph{Proof assistant} & Agda (standard library) & Coq (\texttt{theories/}) & Isabelle (\texttt{HOL/}) \\
\midrule
\emph{Lines of code} & 20,000 & 110,000 & 310,000 \\
%\bottomrule
\end{tabular}
\caption{Comparison of the size of the standard libraries or their equivalents for Agda, Coq and Isabelle. The measurements were taken using \texttt{cloc} (\url{http://cloc.sourceforge.net}) using the Haskell comments parser for Agda source files and the OCaml comments parser for Coq and Isabelle theories.}
\label{tb:Size}
\end{table}

Among the things that make Agda stand out are mutually recursive datatype and function definitions (\emph{induction-recursion}, not supported by Coq), a more experimental and open development model compared to other proof assistants---copatterns, for example, were first implemented in Agda \parencite{abel_wellfounded_2013}, flexible syntax and a \enquote{less is more} philosophy of providing a small kernel with everything else taken care of by libraries: even the \texttt{if … then … else …} construct is defined in a library.

\subsection{Equational reasoning}

%TC:ignore
\AgdaHide{
\begin{code}
module IntroExample where
  open import Data.Nat.Base
  open import Data.Nat.Properties.Simple
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
\end{code}
}
%TC:endignore

In our view, a proof style called \emph{equational reasoning}, made possible by Agda's flexible syntax and used pervasively in the standard library, is another major selling point of the language.

As an example, we will construct a proof of the identity \((p · q) · r = p · (r · q)\) for natural numbers \(p\), \(q\) and \(r\) as one would do using the interactive development environment. We first convince ourselves that the equation holds by writing down its proof by hand, breaking it into small, obvious steps:
\begin{align}
(p · q) · r &= && \text{(associativity)} \\
p · (q · r) &= && \text{(commutativity)} \\
p · (r · q)
\end{align}
We then use those steps as the skeleton of our equational reasoning proof (see \cref{ssc:Equational-reasoning} for details on equational reasoning). The places marked \AgdaSymbol{\{!!\}} represent holes, i.e. justifications that are still missing. The comments indicate how we will go about filling those holes.

\AgdaHide{
\begin{code}
  example : (p q r : ℕ) → (p * q) * r ≡ p * (r * q)
  example p q r = begin
\end{code}
}
\begin{code}
    (p * q) * r  ≡⟨ {! associativity !} ⟩
    p * (q * r)  ≡⟨ {! commutativity !} ⟩
    p * (r * q)  ∎
\end{code}
Thankfully the Agda standard library already contains a proof that multiplication of natural numbers is associative under the name \AgdaFunction{*-assoc}. It shows that for any natural numbers \AgdaBound{p}, \AgdaBound{q} and \AgdaBound{r}, \((p · q) · r = p · (q · r)\)---this is exactly the first step in our handwritten proof (1.1). We use \AgdaFunction{*-assoc} to fill in the first hole in the formal proof:

\AgdaHide{
\begin{code}
  example′ : (p q r : ℕ) → (p * q) * r ≡ p * (r * q)
  example′ p q r = begin
\end{code}
}
\begin{code}
    (p * q) * r  ≡⟨ *-assoc p q r ⟩
    p * (q * r)  ≡⟨ {! commutativity !} ⟩
    p * (r * q)  ∎
\end{code}
In the typeset proof, we wrote that \(p · (q · r) = p · (r · q)\) follows \enquote{by commutativity}. But commutativity really only states that \(q · r = r · q\). Implicitly, we are using the principle that equal subterms can be replaced by equal subterms. In Agda, we must apply this principle, called \emph{congruence}, explicitly. This is one point where formal proofs using equational reasoning deviate from handwritten or typeset proofs.

To be exact, \(p · (q · r) = p · (r · q)\) holds by the following reasoning:
\begin{itemize}
\item Multiplication is \emph{congruent} in both arguments, that is, if \(x = x′\) and \(y = y′\) then \(x · y = x′ · y′\) (in this case we instantiate \(x\) and \(x′\) with \(p\), \(y\) with \(q · r\) and \(y′\) with \(r · q\));
\item \(p = p\) since equality is a \emph{reflexive} relation (i.e. anything is equal to itself); and
\item \(q · r = r · q\) by \emph{commutativity} of multiplication.
\end{itemize}

In Agda, the reflexivity principle is called \AgdaInductiveConstructor{refl}, \AgdaFunction{*-comm} proves that multiplication of natural numbers is commutative and \AgdaFunction{cong₂} \AgdaFunction{\_*\_} shows that it is congruent. They can be written as follows in proof tree notation (with assumptions above the line and conclusion below):

\vspace{.15cm}
\begin{minipage}[b]{1\linewidth}
\centering
\begin{minipage}[b]{0.2\linewidth}
\begin{prooftree}
    \AxiomC{}
    \UnaryInfC{\AgdaInductiveConstructor{refl} \AgdaSymbol{\{}\AgdaBound{x} \AgdaSymbol{=} \AgdaBound{p}\AgdaSymbol{\}} \AgdaSymbol{:} \AgdaBound{p} \AgdaSymbol{=} \AgdaBound{p}}
\end{prooftree}
\end{minipage}
\begin{minipage}[b]{0.36\linewidth}
\begin{prooftree}
    \AxiomC{}
    \UnaryInfC{\AgdaFunction{*-comm} \AgdaBound{x} \AgdaBound{y} \AgdaSymbol{:} \(x · y = y · x\)}
\end{prooftree}
\end{minipage}
\begin{minipage}[b]{0.36\linewidth}
\begin{prooftree}
    \AxiomC{\AgdaBound{f} \AgdaSymbol{:} \(x = x′\)}
    \AxiomC{\AgdaBound{g} \AgdaSymbol{:} \(y = y′\)}
    \BinaryInfC{\AgdaFunction{cong₂} \AgdaFunction{\_*\_} \AgdaBound{f} \AgdaBound{g} \AgdaSymbol{:} \(x · y = x′ · y′\)}
\end{prooftree}
\end{minipage}
\vspace{.5cm}
\end{minipage}
The last rule can be read as \enquote{given a proof \AgdaBound{f} of \(x = x′\) and a proof \AgdaBound{g} of \(y = y′\), we can conclude by \AgdaFunction{cong₂} \AgdaFunction{\_*\_} \AgdaBound{f} \AgdaBound{g} that \(x · y = x′ · y′\) holds}. Instantiating the three rules as appropriate, we can assemble the proof of \(p · (q · r) = p · (r · q)\) as follows:

\begin{minipage}[b]{1\linewidth}
\centering
\vspace{.15cm}
\begin{prooftree}
\AxiomC{}
\UnaryInfC{\AgdaInductiveConstructor{refl} \AgdaSymbol{\{}\AgdaBound{x} \AgdaSymbol{=} \AgdaBound{p}\AgdaSymbol{\}} \AgdaSymbol{:} \(p = p\)}
\AxiomC{}
\UnaryInfC{\AgdaFunction{*-comm} \AgdaBound{q} \AgdaBound{r} \AgdaSymbol{:} \(q · r = r · q\)}
\BinaryInfC{\AgdaFunction{cong₂} \AgdaFunction{\_*\_} \AgdaSymbol{(}\AgdaInductiveConstructor{refl} \AgdaSymbol{\{}\AgdaBound{x} \AgdaSymbol{=} \AgdaBound{p}\AgdaSymbol{\})} \AgdaSymbol{(}\AgdaFunction{*-comm} \AgdaBound{q} \AgdaBound{r}\AgdaSymbol{)} \AgdaSymbol{:} \(p · (q · r) = p · (r · q)\)}
\end{prooftree}
\vspace{.1cm}
\end{minipage}
That is, with \AgdaBound{f} \AgdaSymbol{=} \AgdaInductiveConstructor{refl} \AgdaSymbol{\{}\AgdaBound{x} \AgdaSymbol{=} \AgdaBound{p}\AgdaSymbol{\}} and \AgdaBound{g} \AgdaSymbol{=} \AgdaFunction{*-comm} \AgdaBound{q} \AgdaBound{r}, the third rule constructs the proof of \(p · (q · r) = p · (r · q)\) we were looking for. We can now complete the proof of our original proposition \((p · q) · r = p · (r · q)\) as follows:

\AgdaHide{
\begin{code}
  example″ : (p q r : ℕ) → (p * q) * r ≡ p * (r * q)
  example″ p q r = begin
\end{code}
}
\begin{code}
    (p * q) * r  ≡⟨ *-assoc p q r ⟩
    p * (q * r)  ≡⟨ cong₂ _*_ (refl {x = p}) (*-comm q r) ⟩
    p * (r * q)  ∎
\end{code}
This example demonstrates that the combination of equational reasoning and proof-by-refinement simplifies the process of translating handwritten proofs into formal proofs: we first write down the steps by which the left-hand side of the equation transforms into its right-hand side, and then provide justification for each individual step.


\subsection{Big operators}

How does our library fit into this picture? Big operator libraries have been implemented for Isabelle and Coq, but not for Agda. Our goal was to enable Agda users to express definitions and propositions and prove theorems involving big operators.

As a simple example of what our big operator library permits, consider the \enquote{odd Gauss formula}. In standard mathematical notation, can be written as follows:
\[ ∀n.\;\sum_{\substack{i = 0 \\ \text{\(i\) odd}}}^{2n} i = n² \]
Using the syntax definitions for sums, intervals and filters implemented in our project (see \cref{ch:Impl}), it can be expressed in Agda as
\[
\text{\AgdaSymbol{∀} \AgdaBound{n} \AgdaSymbol{→} \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…} \AgdaBound{n} \AgdaFunction{+} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{odd} \AgdaFunction{]} \AgdaBound{i} \AgdaDatatype{≡} \AgdaBound{n} \AgdaFunction{*} \AgdaBound{n}}%
\label{eq:Intro-Example}
\]
A proof of the \enquote{odd Gauss formula} is presented in \cref{ch:Gauss}. Further proofs using our library in \cref{ch:Binom} and \cref{ch:Semi} demonstrate that we achieve our goal of enabling Agda users to express propositions and write proofs with big operators.

\section{Overview}

In \textbf{\cref{ch:Intro}} we discuss the motivation for the project and describes its main contributions.
\textbf{\cref{ch:Background}} is a tutorial-style introduction to Agda and dependent types in general.
A detailed description of our library is given in \textbf{\cref{ch:Impl}}.
In \textbf{\cref{ch:Semi}} we prove that square matrices over a semiring form a semiring, demonstrating the definitions and lemmas developed in this project.
Finally in \textbf{\cref{ch:Concl}} we discuss previous work and ideas for future research.

\chapter{Background\label{ch:Background}}

In this Chapter, we provide the necessary background for the remainder of the report to make it self-contained.

\cref{sc:Agda-basics} introduces Agda by example. The next three Sections cover some fundamental notions in constructive higher-order logic: we introduce predicates and relations as they are defined in Agda (\cref{sc:Pred-Rel}), discuss provability and decidability and how they correspond to type inhabitation (\cref{sc:Prov-Dec}) and present setoids and the equational reasoning style of writing proofs (\cref{sc:Setoids}). In \cref{sc:Algebra} we review some algebraic properties of binary operators and algebraic structures like monoids and semirings.

\section{Agda basics\label{sc:Agda-basics}}

\AgdaHide{
%TC:ignore
\begin{code}
module Basics where
  open import Level renaming (zero to lzero; suc to lsuc)

  -- infixr 5 _∷_
\end{code}
%TC:endignore
}

This project was implemented in \emph{Agda}, a functional programming language with a dependent type system. \emph{Functional programming} is a declarative paradigm where computation proceeds by evaluating expressions (instead of, say, changing the state of an abstract machine.) In a \emph{dependent} type system, types can contain (depend on) terms---examples of dependent types are given in \cref{ssc:Dependent} and \cref{ssc:Records}.

The advantage of a dependently type language like Agda over non-dependently typed functional languages like \emph{Haskell} \autocite{marlow_haskell_2010} or \emph{ML} \autocite{milner_definition_1997}, is that the type system is more expressive: under the Curry-Howard correspondence, it also serves as a higher-order logic where formulae are encoded as types and terms inhabiting those types witness derivations \autocite{howard_formulae-as-types_1980}. The disadvantage is that type inference is undecidable, so most terms need type annotations.

We now introduce the syntax of Agda. The following sections explain how Agda can be used to write theorems and check proofs.

\subsection{Small types and functions\label{ssc:Small}}

Truth values (Booleans) can be defined in Agda as follows:

%TC:ignore
\begin{code}
  data Bool : Set where
    true   :  Bool
    false  :  Bool
\end{code}
%TC:endignore

We introduce a new type \AgdaDatatype{Bool} with two constructors, \AgdaInductiveConstructor{true} and \AgdaInductiveConstructor{false}. Both construct elements of \AgdaDatatype{Bool}, so that is the type we annotate them with (after the colon). It may come as a surprise that the type \AgdaDatatype{Bool} itself needs an annotation, too. In Agda, the type of small types is called \AgdaPrimitiveType{Set}. Since \AgdaDatatype{Bool} is a small type, we declare it to be of type \AgdaPrimitiveType{Set}. In \cref{ssc:Hierarchy} we introduce types that are not contained in \AgdaPrimitiveType{Set}.

Let us now write a function using this newly introduced datatype. \AgdaFunction{not} flips its Boolean argument:

%TC:ignore
\begin{code}
  not : Bool → Bool
  not true   =  false
  not false  =  true
\end{code}
%TC:endignore

This function takes a \AgdaDatatype{Bool} and returns a \AgdaDatatype{Bool}, so the type of the function as a whole is \AgdaDatatype{Bool} \AgdaSymbol{→} \AgdaDatatype{Bool}. The function is defined by pattern matching: the result of the function is the term on the right-hand side of the equality sign if its input matches the left-hand side.

Note that the pattern matching must cover all possible cases. More generally speaking, all Agda functions must be \emph{total}, that is, defined on all values of its argument types. Partiality can be modelled either by restricting the domain of an argument using dependent types (see \cref{ssc:Dependent}) or using \AgdaDatatype{Maybe} \AgdaBound{A} as a return type for a partial function into type \AgdaBound{A}.%
\footnote{\AgdaDatatype{Maybe} \AgdaBound{A} has two constructors, \AgdaInductiveConstructor{just} \AgdaSymbol{:} \AgdaSymbol{(}\AgdaBound{x} \AgdaSymbol{:} \AgdaBound{A}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{Maybe} \AgdaBound{A} representing a successful computation of a value of type \AgdaBound{A} and \AgdaInductiveConstructor{nothing} \AgdaSymbol{:} \AgdaDatatype{Maybe} \AgdaBound{A} representing a failed computation.}

Agda identifiers can contain Unicode symbols, which makes it possible to use notation familiar from mathematics in Agda code. The function \AgdaFunction{\_∧\_} computes the logical conjunction of its inputs:

%TC:ignore
\begin{code}
  _∧_ : Bool → _ → Bool
  true  ∧ true  = true
  _     ∧ _     = false
\end{code}
%TC:endignore

An underscore (the symbol \enquote{\_}) can be interpreted in three different ways in Agda, depending on the context of its use. This slightly contrived example covers them all:

\begin{description}
\item[In an identifier] like \AgdaFunction{\_∧\_}, the underscores indicate where the function or type expects its arguments. This allows programmers to introduce new infix and mixfix operators. As an example for a mixfix operator, the Agda standard library defines \AgdaFunction{if\_then\_else\_} which takes Boolean, a term of some type and another term of the same type and returns the appropriate value based on whether the Boolean equals \AgdaInductiveConstructor{true} or \AgdaInductiveConstructor{false}.
\textcite{danielsson_parsing_2011} presents a general framework for parsing mixfix operators, of which infix operators are a special case.
\item[In place of a term or type] an underscore stands for a value that is to be inferred by Agda. In the type of our function, \AgdaDatatype{Bool} \AgdaSymbol{→} \AgdaSymbol{\_} \AgdaSymbol{→} \AgdaDatatype{Bool}, the underscore marks the type of the second argument to \AgdaFunction{\_∧\_}. It is easily resolved: in the first pattern, the second argument is matched with \AgdaInductiveConstructor{true}, which is a constructor for the type \AgdaDatatype{Bool}. The underscore must therefore stand for \AgdaDatatype{Bool}.
\item[As a pattern] the underscore matches anything. It acts like a fresh pattern variable that cannot be referred to. The definition of \AgdaFunction{\_∧\_} can thus be read as \enquote{the conjunction of two Booleans is true if both arguments are true; in any other case, the result is false.}
\end{description}

Let us consider a type with more structure. A natural number is either zero, or the successor of some natural number. In Agda, this inductive definition is written as:

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

Pattern variables like \AgdaBound{m} and \AgdaBound{n} are bound in the function body. They are substituted for the values passed to the function when it is evaluated.

Note that Agda functions defined on inductive types must not only be total, but also \emph{terminating}.%
\footnote{Functions defined on \emph{coinductive} types, on the other hand, must be \emph{productive}. \textcite{altenkirch_termination_2010} discusses the issue of termination checking functions on nested inductive and coinductive types.} %
Since termination checking is undecidable in general, Agda checks whether the arguments to the recursive call are structurally smaller than the arguments to the caller as a safe syntactic approximation to termination.

This is clearly the case in the recursive case of \AgdaFunction{\_+\_}: the arguments to the caller are \AgdaInductiveConstructor{suc} \AgdaBound{m} and \AgdaBound{n} whereas those passed used in the recursive call are \AgdaBound{m} and \AgdaBound{n}. Structurally, \AgdaBound{m} is smaller than \AgdaInductiveConstructor{suc} \AgdaBound{m} so Agda can infer that the function terminates on all inputs. A formal definition of \emph{structurally smaller} is given in \textcite{coquand_pattern_1992}.

\subsection{The type hierarchy and universe polymorphism\label{ssc:Hierarchy}}

Both \AgdaDatatype{Bool} and \AgdaDatatype{ℕ} as well as all the functions we have seen so far could have been written in a very similar way in Haskell or ML, modulo syntax. We will now see how Agda is different from non-dependently typed functional languages.

Every type in Agda resides somewhere in a type universe with countably infinite levels. In other words, if a type \AgdaBound{A} is well-formed, then there exists some level \AgdaBound{a} such that \AgdaBound{A} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaBound{a}. The reason for introducing a hierarchy of types in the first place is that allowing a typing judgement like \AgdaPrimitiveType{Set} \AgdaSymbol{:} \AgdaPrimitiveType{Set} makes the system logically inconsistent.%
\footnote{A judgement like \AgdaPrimitiveType{Set} \AgdaSymbol{:} \AgdaPrimitiveType{Set} in a type theory makes it possible to prove any proposition. Equivalently, it implies that every type, even \AgdaDatatype{⊥}, is inhabited. Jean-Yves Girard first pointed this out in his doctoral thesis \autocite{girard_interpretation_1972}. Thierry Coquand wrote a very readable introduction to the issue for the Stanford Encyclopedia of Philosophy, relating it, amongst others, to Russel's paradox \autocite{coquand_type_2014}. The approach taken by Coq and Agda to avoid Girard's paradox via an infinite hierarchy of types closely resembles Grothendieck's solution to similar issues in set theory by introducing what are now called \emph{Grothendieck universes} \autocite{artin_theorie_1972}.}

\AgdaDatatype{Bool} and \AgdaDatatype{ℕ} are examples of small types, which is expressed in Agda as \AgdaDatatype{Bool} \AgdaDatatype{ℕ} \AgdaSymbol{:} \AgdaPrimitiveType{Set} (note that we can give type declarations for terms of the same type in one line in this way.) \AgdaPrimitiveType{Set} is a synonym for \AgdaPrimitiveType{Set} \AgdaNumber{0}, which is itself of type \AgdaPrimitiveType{Set} \AgdaNumber{1}.\footnote{We use numbers \AgdaNumber{0}, \AgdaNumber{1}, \AgdaNumber{2} to denote universe levels for brevity here. In actual code, elements of the opaque type \AgdaPrimitiveType{Level} can only be constructed using the postulated functions \AgdaFunction{lzero} and \AgdaFunction{lsuc}.} This gives rise to an infinite predicative hierarchy of types, which approximates \AgdaPrimitiveType{Set} \AgdaSymbol{:} \AgdaPrimitiveType{Set} in the limit:
%(XXX explain predicativity, difference between Agda and Coq)
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
Before we explain this datatype declaration in detail, we consider an examples first. The list \AgdaFunction{bools} contains Boolean values. Here the carrier type of the list, \AgdaBound{A}, is instantiated to \AgdaDatatype{Bool}.

%TC:ignore
\begin{code}
  bools : List Bool
  bools = true ∷ (false ∷ ((true ∧ false) ∷ []))
\end{code}
%TC:endignore
In the datatype declaration of \AgdaDatatype{List}, the names \AgdaBound{a} and \AgdaBound{A} are left of the colon. They are global to the constructors of the datatype and called \emph{parameters}. The parameter \AgdaBound{a} is written in curly braces, which marks it as an \emph{implicit} parameter. This means that Agda will try to infer its value if it is not given explicitly.

\AgdaDatatype{Bool} has type \AgdaPrimitiveType{Set} \AgdaNumber{0}, so Agda correctly infers that in the type of \AgdaFunction{bools}, \AgdaBound{a} must be \AgdaNumber{0}. If we wanted to be explicit, we could have written the declaration as \AgdaFunction{bools} \AgdaSymbol{:} \AgdaDatatype{List} \AgdaSymbol{\{}\AgdaNumber{0}\AgdaSymbol{\}} \AgdaDatatype{Bool} instead.

Why is the parameter \AgdaBound{a} necessary at all? Since our definition of \AgdaDatatype{List} abstracts over the level of its carrier type, we can also build lists that live higher up in the type hierarchy. We might for example want to create a list of types:

%TC:ignore
\begin{code}
  types : List Set
  types = Bool ∷ (((ℕ → ℕ) → Bool) ∷ [])
\end{code}
%TC:endignore
Here the carrier type of the list is instantiated as \AgdaPrimitiveType{Set}, which is itself of type \AgdaPrimitiveType{Set} \AgdaNumber{1}. The value of the implicit parameter \AgdaBound{a} is inferred as level \AgdaNumber{1}. Note that the function type \AgdaSymbol{(}\AgdaDatatype{ℕ} \AgdaSymbol{→} \AgdaDatatype{ℕ}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{Bool} is also a small type.

Lists defined in this way are \emph{universe polymorphic}, meaning that the universe level at which any particular list resides depends on its parameters. Making a parameter or argument of type \AgdaPrimitiveType{Level} implicit is common practice in Agda. Most of the time, the type checker can infer universe levels without ambiguity.

\subsection{Dependent types and indexed type families\label{ssc:Dependent}}

We now turn to the classic example of a dependent datatype (or \emph{indexed family of types}): fixed-length lists, or \emph{vectors}:%
\footnote{Lists and vectors have the same constructors, so depending on the context, \AgdaInductiveConstructor{[]} and \AgdaInductiveConstructor{\_∷\_} may create a list or a vector. If a constructor is used in a context where its type is ambiguous, the full constructor name (such as \AgdaInductiveConstructor{List.[]}) must be given.}

%TC:ignore
\begin{code}
  data Vec {a} (A : Set a) : ℕ → Set a where
    []   : Vec A zero
    _∷_  : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}
%TC:endignore
The parameters (on the left-hand side of the colon in the type declaration) are the same as for \AgdaDatatype{List}, a type level \AgdaBound{a} and a type \AgdaBound{A}. Note that we have not specified the type of \AgdaBound{a}---Agda infers that it must be a \AgdaPrimitiveType{Level}. In addition to the parameters, the type \AgdaDatatype{Vec} is \emph{indexed} by a natural number, hence the \AgdaDatatype{ℕ} on the right-hand side of the colon. While parameters are the same for all constructors, indices may differ: the constructor \AgdaInductiveConstructor{[]} returns a \AgdaInductiveConstructor{zero}-length vector, while \AgdaInductiveConstructor{\_∷\_} takes an element and a vector of length \AgdaBound{n} and returns a vector of length \AgdaInductiveConstructor{suc} \AgdaBound{n}.

The vector append function \AgdaFunction{\_++\_} demonstrates how dependent types can be used to enforce invariants. It takes two vectors of length \AgdaBound{m} and \AgdaBound{n}, respectively, and returns a vector of length \AgdaBound{m} \AgdaFunction{+} \AgdaBound{n}. The fact that the type checker accepts the definition of this function means that the length of the vector that is returned always is the sum of the lengths of the input vector.

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
But what about totality? Earlier we said that the patterns of a function must cover all possible arguments of its type. If we look close enough, we can see that this principle is not violated here even though there is no pattern for the empty vector. The reason is that the constructor for the empty vector has type \AgdaInductiveConstructor{[]} \AgdaSymbol{:} \AgdaDatatype{Vec} \AgdaBound{A} \AgdaInductiveConstructor{zero}. Agda knows that \AgdaInductiveConstructor{suc} \AgdaBound{n} and \AgdaInductiveConstructor{zero} cannot be unified, so we do not have to (and indeed cannot) supply a pattern for the empty list, which is exactly what we wanted. This is a first example of the powerful interplay between dependent types and pattern matching.
%Later we will see dotted patterns, absurd patterns and the \AgdaKeyword{with} construct.

Lastly, we consider the type of finite sets \AgdaDatatype{Fin}, indexed by a natural number:

%TC:ignore
\begin{code}
  data Fin : ℕ → Set where
    zero  : {n : ℕ} → Fin (suc n)
    suc   : {n : ℕ} → Fin n → Fin (suc n)
\end{code}
%TC:endignore
One way to think about this type is that its value represents a natural number with its index as an upper bound. The type \AgdaDatatype{Fin}~\AgdaBound{n} has exactly \AgdaBound{n} different values, representing the numbers up to \(n-1\). \AgdaDatatype{Fin} \AgdaInductiveConstructor{zero} is empty; there is no way to construct a value of this type.

A bounded natural number can be used as an index into a vector. This lets us leverage the type system to eliminate out-of-bounds handling. Consider the (slightly contrived definition of a) function \AgdaFunction{lookup}, which takes a position bounded by \AgdaBound{n} and a vector of length \AgdaBound{n} and returns the element at this position:

%TC:ignore
\begin{code}
  lookup : ∀ {n a} {A : Set a} → Fin n → Vec A n → A
  lookup {.zero}  ()       []
  lookup          zero     (x ∷ xs) = x
  lookup          (suc n)  (x ∷ xs) = lookup n xs
\end{code}
%TC:endignore
What is going on in the first pattern? Firstly, it shows that we can match against implicit arguments by position. Here we use the pattern \AgdaSymbol{\{}.\AgdaInductiveConstructor{zero}\AgdaSymbol{\}} to match the argument \AgdaBound{n}. The curly braces indicate that we are matching against an implicit argument; the dot before the pattern marks this pattern as the unique value of the correct type. It is unique in this case because the constructor of the empty vector \AgdaInductiveConstructor{[]} \AgdaSymbol{:} \AgdaDatatype{Vec} \AgdaBound{A} \AgdaInductiveConstructor{zero} appears in the same pattern, which forces the unification of \AgdaBound{n} with \AgdaInductiveConstructor{zero}. Note that \emph{dotted patterns} do not have to be implicit, and that implicit arguments can also be matched against by name.

Secondly, since \AgdaBound{n} is unified with \AgdaInductiveConstructor{zero}, the position (the first non-implicit argument) would have to be of type \AgdaDatatype{Fin} \AgdaInductiveConstructor{zero}. But there is no value of this type! Agda's type checker can infer this and allows us to match this impossible value with \AgdaBound{()}, the \emph{absurd pattern}. No right-hand side is given for absurd patterns because they are never matched.%
\footnote{Note that in this particular example, it is not necessary to write down the first pattern. As with the function \AgdaFunction{head}, Agda can infer that the second and third pattern cover all possible inputs. However, in more complicated pattern matches, the absurd pattern is sometimes needed. It allows us to tell the totality checker explicitly which argument it is that cannot possibly be given.}


\subsection{Record types\label{ssc:Records}}

The \AgdaKeyword{record} keyword lets us bundle terms and types together in a convenient manner. The type of a record field can depend on the values of any other field preceding it in the definition. A dependent pair type (or \emph{Sigma type}) can be defined like this:

%TC:ignore
\begin{code}
  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      fst  : A
      snd  : B fst
\end{code}
%TC:endignore
The level of a record is the least upper bound \AgdaBound{a} \AgdaFunction{⊔} \AgdaBound{b} of it fields' levels. Giving a \AgdaKeyword{constructor} is optional in general but required for pattern matching. It also makes defining new values less verbose---compare \AgdaFunction{pair₀} and \AgdaFunction{pair₁} in the next example.

In the type declaration of \AgdaDatatype{Σ}, the name \AgdaBound{B} is given to a function which takes a \emph{value} of type \AgdaBound{A} and returns a \emph{type} at level \AgdaBound{b}. The type of \AgdaField{snd} is defined as \AgdaBound{B} \AgdaBound{fst}, so it \emph{depends} on the value of \AgdaField{fst}. That is why \AgdaDatatype{Σ} is called a dependent pair.% This type will become important in the next sections when predicates and existential quantifiers are discussed.
For now we will restrict ourselves to building non-dependent pairs, which means that we will ignore the \AgdaBound{A}-typed parameter to \AgdaBound{B}. We can use \AgdaDatatype{Σ} to define non-dependent pairs like this:

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
As a record type, \AgdaDatatype{Σ} can be deconstructed in many ways. The name of the type and the name of the field, separated by a dot, can be used to access that field (see \AgdaFunction{fst₀}). Alternatively, \AgdaKeyword{open} followed by the name of the type can be used to bring the names of the field accessors into scope (see \AgdaFunction{fst₁}). The fields themselves can be brought into scope by opening the type followed by the value whose fields we want to access (see \AgdaFunction{fst₂}). Note that \enquote{\AgdaKeyword{let} … \AgdaKeyword{in} \AgdaBound{x}} and \enquote{\AgdaBound{x}~\AgdaKeyword{where} …} can be used almost interchangeably. In the last example, we pattern match on the constructor of the type to extract its fields (see \AgdaFunction{fst₃}).

%TC:ignore
\begin{code}
  fst₀ fst₁ fst₂ fst₃ : ∀ {a b} {A : Set a} {B : Set b} → A × B → A
  fst₀ = Σ.fst
  fst₁ = let open Σ in fst
  fst₂ p = fst where open Σ p
  fst₃ (x , _) = x
\end{code}
%TC:endignore


\section{Predicates and relations\label{sc:Pred-Rel}}

In this Section, we will see how predicates and relations are expressed in a dependent type system by example. We will then introduce the notion of \emph{constructive logic} and how it relates to dependently typed programs.

From this point on, we will call some functions \enquote{proofs} and some types \enquote{theorems}. The justification for this lies in the Curry-Howard correspondence, for which we will provide some intuition in this Chapter and the next. For a mathematically exact and systematic take on the Curry-Howard correpondence, see \autocite{sorensen_lectures_2006}.

\subsection{Predicates}

%TC:ignore
\AgdaHide{
\begin{code}
module Predicates where
  open import Level using (_⊔_)

  open import Data.Fin
  open import Data.Nat hiding (_⊔_)
  open import Data.Nat.DivMod
  open import Data.Product hiding (∃; curry; uncurry)
  open import Relation.Nullary
  open import Relation.Unary using (Pred; Decidable)
--  open import Relation.Binary.PropositionalEquality using (_≡_)

  infix 4 _≡_
\end{code}
}
%TC:endignore

A predicate expresses some property of a term. The type of a predicate \AgdaFunction{P} over a type \AgdaDatatype{A} is \AgdaFunction{P}~\AgdaSymbol{:} \AgdaDatatype{A} \AgdaSymbol{→} \AgdaPrimitiveType{Set}. The value of a predicate \AgdaFunction{P} \AgdaBound{x} can be thought of as the \emph{evidence} that \AgdaFunction{P} holds for \AgdaBound{x} \AgdaSymbol{:} \AgdaDatatype{A}.
We will look at a predicate \AgdaDatatype{Even}~\AgdaSymbol{:} \AgdaDatatype{ℕ} \AgdaSymbol{→} \AgdaPrimitiveType{Set} as a warm-up, followed by a discussion of propositional equality, \AgdaDatatype{\_≡\_}. For a discussion of a more involved predicate, \AgdaDatatype{Collatz}~\AgdaSymbol{:} \AgdaDatatype{ℕ} \AgdaSymbol{→} \AgdaPrimitiveType{Set}, see \cref{ch:Collatz}.

\AgdaDatatype{Even} \AgdaBound{n} provides evidence that \AgdaBound{n} is an even number. One way of defining this predicate is by stating that any even number is either equal to zero, or it is the successor of the successor of an even number:

%TC:ignore
\begin{code}
  data Even : ℕ → Set where
    zero-even  : Even zero
    ss-even    : {n : ℕ} → Even n → Even (suc (suc n))
\end{code}
%TC:endignore
Using this definition, we can now provide evidence that zero and four are even numbers:

%TC:ignore
\begin{code}
  Even‿0 : Even 0
  Even‿0 = zero-even

  Even‿4 : Even 4
  Even‿4 = ss-even (ss-even zero-even)
\end{code}
%TC:endignore
Since for some \AgdaBound{n} \AgdaSymbol{:} \AgdaDatatype{ℕ}, \AgdaDatatype{Even} \AgdaBound{n} is a datatype, the evidence it represents can be analysed by pattern matching in proofs.

Next we look at \emph{propositional equality}, written as \AgdaDatatype{\_≡\_} in Agda.\footnote{The variant of propositional equality presented here is attributed to Christine Paulin-Mohring \autocite{dybjer_what_2006}.} The parameterised predicate \AgdaDatatype{\_≡\_} \AgdaBound{x} expresses the property of \enquote{being equal to \AgdaBound{x}}. Two elements of the same type are propositionally equal if they can be shown to reduce to the same value.

%TC:ignore
\begin{code}
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x
\end{code}
%TC:endignore
The parameterised predicate \AgdaDatatype{\_≡\_} has only one constructor called \AgdaInductiveConstructor{refl}.%
\footnote{Note that we call \AgdaDatatype{\_≡\_} a \emph{parameterised predicate}, not a \emph{relation}, because it has type \AgdaSymbol{(}\AgdaBound{x} \AgdaSymbol{:} \AgdaBound{A}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaBound{A} \AgdaSymbol{→} \AgdaPrimitiveType{Set} \AgdaBound{a} rather than \AgdaBound{A} \AgdaSymbol{→} \AgdaBound{A} \AgdaSymbol{→} \AgdaPrimitiveType{Set} \AgdaBound{a} (the type of homogeneous relations of \AgdaBound{A}, see \cref{ssc:Relations}). There is an equivalent definition of propositional equality as a relation, but the one shown here is easier to use in proofs.} %
In order to create an inhabitant of the propositional equality type, we \emph{must} use this constructor.
It requires that its two arguments have the same value. Therefore, in order to obtain an inhabitant of \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{y}, \AgdaBound{x} and \AgdaBound{y} must be shown to reduce to the same value.

Evaluating a function with equal arguments should always yield equal results. This property of a homogeneous relation is called \emph{congruence}, and it can be proved for any single argument function \AgdaBound{f} as follows:

%TC:ignore
\begin{code}
  cong :  ∀ {a b} {A : Set a} {B : Set b}
          (f : A → B) {x y} → x ≡ y → f x ≡ f y
  cong f {x} {.x} refl = refl
\end{code}
%TC:endignore
Let us consider this proof step by step. We match the argument of type \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{y} with its only constructor, \AgdaInductiveConstructor{refl}. This tells the type checker that \AgdaBound{x} and \AgdaBound{y} must be equal as \AgdaInductiveConstructor{refl} \AgdaSymbol{:} \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{x}, and replaces all occurrences of \AgdaBound{y} by \AgdaBound{x} for this clause. To make this clearer we also pattern match against the implicit parameters \AgdaBound{x} and \AgdaBound{y}. Argument \AgdaBound{x} is simply matched against a variable \AgdaBound{x}. The dotted pattern for \AgdaBound{y} is revealing: since the pattern \AgdaInductiveConstructor{refl} forces \AgdaBound{x} and \AgdaBound{y} to be equal, the unique value that \AgdaBound{y} can take is \AgdaBound{x}. This pattern match against \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{y} also has the effect of \emph{rewriting} the type of the result expected on the right-hand side of the equals sign to \AgdaBound{f} \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{f} \AgdaBound{x}. But as \AgdaBound{f} \AgdaBound{x} and \AgdaBound{f} \AgdaBound{x} are trivially equal, we can close the prove by simply using \AgdaInductiveConstructor{refl}.


\subsection{Relations\label{ssc:Relations}}

%TC:ignore
\AgdaHide{
\begin{code}
module Relations where
  open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

  open import Data.Nat hiding (_⊔_; _*_)
  open import Data.Nat.DivMod
  open import Data.Product hiding (∃; curry; uncurry)
  open import Relation.Binary.PropositionalEquality
\end{code}
}
%TC:endignore

Usually in mathematics a relation between two sets is defined as a subset of the Cartesian product of the two sets. In a dependent type theory, a binary relation between types \AgdaDatatype{A} \AgdaSymbol{:} \AgdaPrimitiveType{Set} and \AgdaDatatype{B} \AgdaSymbol{:} \AgdaPrimitiveType{Set} has the type \AgdaDatatype{A} \AgdaSymbol{→} \AgdaDatatype{B} \AgdaSymbol{→} \AgdaPrimitiveType{Set}.
It is not hard to show that this type is isomorphic to \AgdaDatatype{A} \AgdaDatatype{×} \AgdaDatatype{B} \AgdaSymbol{→} \AgdaPrimitiveType{Set} (see \cref{sc:Curry} for a formal proof).
Note that relations and predicates are closely related: a relation can be thought of as a predicate abstracted over some argument, and any relation can be applied to one argument to give a predicate.

We will restrict our attention to the special case of relations between inhabitants of the same type, called \emph{homogeneous} relations. Formally, we can define predicates and homogeneous relations with an explicit universe parameter \AgdaBound{ℓ} as follows:

%TC:ignore
\begin{code}
  Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Pred A ℓ = A → Set ℓ

  Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = A → A → Set ℓ
\end{code}
%TC:endignore
The evenness predicate from the previous Section can now be typed as \AgdaDatatype{Even} \AgdaSymbol{:} \AgdaDatatype{Pred} \AgdaDatatype{ℕ} \AgdaFunction{lzero}. As an example, \emph{Divisibility} is a familiar relation with a straightforward definition in Agda. It uses multiplication, so we define that first:

%TC:ignore
\begin{code}
  _*_ : ℕ → ℕ → ℕ
  zero   * n = zero
  suc m  * n = n + m * n
\end{code}
%TC:endignore
Now we can give a definition for the divisibility relation, which translates to \enquote{\(m\) divides \(n\) if you can provide a \(q\) such that \(n \equiv q m\)}.

%TC:ignore
\begin{code}
  data _∣_ : ℕ → ℕ → Set {- equivalently, Rel ℕ lzero -} where
    divides : {m n : ℕ} (q : ℕ) (eq : n ≡ q * m) → m ∣ n
\end{code}
%TC:endignore
The following proof demonstrates how this relation can be instantiated. It shows that \AgdaNumber{1} divides any natural number \AgdaBound{n}:

%TC:ignore
\begin{code}
  1-divides-any : ∀ n → 1 ∣ n
  1-divides-any n = divides {1} {n} n n≡n*1
    where
      n≡n*1 : ∀ {n} → n ≡ n * 1
      n≡n*1 {zero}   = refl
      n≡n*1 {suc n}  = cong suc n≡n*1
\end{code}
%TC:endignore
The equality \AgdaBound{n} \AgdaDatatype{≡} \AgdaBound{n} \AgdaFunction{*} \AgdaNumber{1} may seem rather obvious, and yet we need to prove it separately. This is because we defined multiplication by induction on its first parameter, so \AgdaNumber{1} \AgdaFunction{*} \AgdaBound{n} normalises to \AgdaBound{n} \AgdaFunction{+} \AgdaInductiveConstructor{zero} but \AgdaBound{n} \AgdaFunction{*} \AgdaNumber{1} cannot be evaluated further---it is \enquote{stuck}.

\AgdaFunction{n≡n*1} is a proof of the required equality by induction. The base case is \(\AgdaBound{n} = \AgdaInductiveConstructor{zero}\). By the definition of \AgdaFunction{\_*\_}, \(\AgdaInductiveConstructor{zero}\;\AgdaFunction{*}\;\AgdaNumber{1} = \AgdaInductiveConstructor{zero}\) and the equality holds. In the inductive step, we need to show that \AgdaInductiveConstructor{suc} \AgdaBound{n} \AgdaDatatype{≡} \AgdaInductiveConstructor{suc} \AgdaBound{n} \AgdaFunction{*} \AgdaFunction{1}. The right-hand side evaluates to \AgdaNumber{1} \AgdaFunction{+} \AgdaBound{n} \AgdaFunction{*} \AgdaNumber{1}, which in turn evaluates to \AgdaInductiveConstructor{suc} (\AgdaBound{n} \AgdaFunction{*} \AgdaNumber{1}).
The inductive hypothesis, \AgdaFunction{n≡n*1} \AgdaSymbol{\{}\AgdaBound{n}\AgdaSymbol{\}} proves that \AgdaBound{n} \AgdaDatatype{≡} \AgdaBound{n} \AgdaFunction{*} \AgdaNumber{1}. Our goal in the inductive step is show that \AgdaInductiveConstructor{suc} \AgdaBound{n} \AgdaDatatype{≡} \AgdaInductiveConstructor{suc} (\AgdaBound{n} \AgdaFunction{*} \AgdaNumber{1}). The latter follows from the former by \AgdaFunction{cong}ruence.


\section{Provability and decidability\label{sc:Prov-Dec}}

In this Section, we will make the relationship between Agda's type system and constructive logic more explicit, using types, predicates and relations from the previous Section as examples.

\AgdaHide{
%TC:ignore
\begin{code}
module Truth where
  open import Data.Nat

  data Even : ℕ → Set where
    zero-even : Even zero
    ss-even   : {n : ℕ} → Even n → Even (suc (suc n))
\end{code}
%TC:endignore
}

\subsection{Type inhabitation}

We proved in the previous Section that four is an even number by giving a term of type \AgdaDatatype{Even} \AgdaNumber{4}. The term we wrote down, \AgdaInductiveConstructor{ss-even} \AgdaSymbol{(}\AgdaInductiveConstructor{ss-even} \AgdaInductiveConstructor{zero-even}\AgdaSymbol{)}, explicitly constructs an element of \AgdaDatatype{Even} \AgdaNumber{4}. The fact the we were able to define a term of this type means that the type is \emph{inhabited}, that is, it has at least one element.

Type inhabitation translates to \emph{provability} in the constructive logic corresponding to Agda's type system: a type is shown to be inhabited if a term of that type can be given; in a constructive logic, a proposition is considered true when a constructive proof can be given for that proposition.

A proof of classical logic is a constructive proof if it does not use the law of excluded middle \((A ∨ ¬ A)\) or proof by contradiction / double negation elimination \((¬ ¬ A → A)\). The law of contradiction \(((A → B) → (A → ¬ B) → ¬ A)\) and \emph{ex falso quodlibet} \((¬ A → A → B)\) are allowed.

One consequence of disallowing proof by contradiction is that in constructive logic, \(¬ (∀ x. P(x)) → (∃ x. ¬ P(x))\) is not a theorem. In order to prove that there exists some element with a certain property, it not sufficient to show that it is impossible for it not to exist: we must construct that element explicitly.

Let us consider the following definition:

%TC:ignore
\begin{code}
  data ⊥ : Set where
\end{code}
%TC:endignore
The type \AgdaDatatype{⊥} (pronounced \enquote{bottom}) has no constructors, yet without termination checking we could define a function that just calls itself to inhabit \AgdaDatatype{⊥}. But this requires general recursion, which is not allowed in Agda because of the termination requirement. Therefore \AgdaDatatype{⊥} has no inhabitants, which is why it is often called the \emph{empty type}.

A type with no elements is useless from a computational perspective: it can neither be constructed nor deconstructed, so we cannot write functions which operate on it. It does, however, make for a useful definition of emptiness. We said just now that it is impossible to create an element of type \AgdaDatatype{⊥}. But \emph{ex falso quodlibet} means that we can derive anything, even \AgdaDatatype{⊥}, from an absurd assumption:

%TC:ignore
\begin{code}
  ¬Even‿1 : Even 1 → ⊥
  ¬Even‿1 ()
\end{code}
%TC:endignore
Here the \emph{only} pattern is an absurd pattern. One is neither zero nor the successor of the successor of any natural number, so an argument of type \AgdaDatatype{Even} \AgdaNumber{1} is absurd. We do not need to supply a right-hand side of the definition because an argument of type \AgdaDatatype{Even} \AgdaNumber{1} can never be given.

We are allowed to give this undefined return value any type we like. Setting this return type to \AgdaDatatype{⊥} carries a special meaning: only functions where the arguments are empty types can return the empty type, so the fact that we can define a function \AgdaBound{A} \AgdaSymbol{→} \AgdaDatatype{⊥} for some type \AgdaBound{A} means that \AgdaBound{A} must be empty.
This is the motivation for termination checking: without it, any function could have \AgdaDatatype{⊥} as its return type. With termination checks in place, a function into the empty type proves that its domain is empty.

The following definition is simply a shortcut for the type of empty types:

%TC:ignore
\begin{code}
  ¬_ : ∀ {p} → Set p → Set p
  ¬ P = P → ⊥
\end{code}
%TC:endignore
This lets us write the type of \AgdaFunction{¬Even‿1} more succinctly as \AgdaFunction{¬}~\AgdaDatatype{Even}~\AgdaNumber{1}.

\subsection{Decidability}

The notion of relation and predicate as introduced above is very general. One question we may ask is whether there exists a terminating decision procedure for a given relation or predicate. In the case of a predicate \AgdaDatatype{P} \AgdaSymbol{:} \AgdaDatatype{A} \AgdaSymbol{→} \AgdaPrimitiveType{Set}, a decision procedure would be a function which for any argument \AgdaBound{x} \AgdaSymbol{:} \AgdaDatatype{A} returns either an inhabitant of type \AgdaDatatype{P} \AgdaBound{x} (evidence that the predicate holds) or an inhabitant of type \AgdaDatatype{¬} \AgdaDatatype{P} \AgdaBound{x} (evidence that the predicate does not hold).

We can capture decidability in a type as follows:

%TC:ignore
\begin{code}
  data Dec {p} (P : Set p) : Set p where
    yes  : (p   :    P) → Dec P
    no   : (¬p  : ¬  P) → Dec P
\end{code}
%TC:endignore
For example, in order to show that the predicate \AgdaDatatype{Even} is decidable on all natural numbers, we can define a function of type \AgdaSymbol{∀} \AgdaBound{n} \AgdaSymbol{→} \AgdaDatatype{Dec} \AgdaSymbol{(}\AgdaDatatype{Even} \AgdaBound{n}\AgdaSymbol{)}:

%TC:ignore
\begin{code}
  even : ∀ n → Dec (Even n)
  even 0  = yes zero-even
  even 1  = no (λ ())
  even (suc (suc n)) with even n
  ... | yes p  = yes (ss-even p)
  ... | no ¬p  = no (ss-odd ¬p)
    where
      ss-odd : ∀ {n} → ¬ Even n → ¬ Even (suc (suc n))
      ss-odd ¬ps (ss-even p) = ¬ps p
\end{code}
%TC:endignore
We have already covered the two base cases before: zero is clearly even and one is clearly not. The induction step is where things get interesting. Using a \AgdaKeyword{with}-clause, we pattern match on whether \AgdaBound{n} is even. If yes, then we can easily construct a proof of \AgdaDatatype{Even} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{n}\AgdaSymbol{))} by applying \AgdaInductiveConstructor{ss-even} to the proof of \AgdaDatatype{Even} \AgdaBound{n}.

Otherwise, we build a proof of \AgdaFunction{¬} \AgdaDatatype{Even} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{n}\AgdaSymbol{))} from a element of \AgdaFunction{¬} \AgdaDatatype{Even} \AgdaBound{n} using \AgdaFunction{ss-odd}. Since \AgdaFunction{¬} \AgdaBound{A} is just an abbreviation for \AgdaBound{A} \AgdaSymbol{→} \AgdaDatatype{⊥}, the type of \AgdaFunction{ss-odd} can also be written as
\AgdaSymbol{∀} \AgdaSymbol{\{}\AgdaBound{n}\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaDatatype{Even} \AgdaBound{n} \AgdaSymbol{→} \AgdaDatatype{⊥}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{Even} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{n}\AgdaSymbol{))} \AgdaSymbol{→} \AgdaDatatype{⊥}. The given pattern matches
\AgdaBound{¬ps} \AgdaSymbol{:} \AgdaDatatype{Even} \AgdaBound{n} \AgdaSymbol{→} \AgdaDatatype{⊥} and
\AgdaBound{p} \AgdaSymbol{:} \AgdaDatatype{Even} \AgdaBound{n}. All we need to do to derive a contradiction is to apply \AgdaBound{¬ps} to \AgdaBound{p}.


\section{Equivalences and setoids\label{sc:Setoids}}

The main use case of the \AgdaModule{Bigop} library is to prove equalities like the Binomial Theorem \autocite[][Equation 5.13, page 163]{graham_concrete_1994}: \[ (1 + x)^n = \sum_{k = 0}^n \binom{n}{k} \; x^k \]
In dependently typed languages, we often use the more general notions of equivalence and setoid in place of equality. These will be discussed in this Section.

\subsection{Equivalences\label{ssc:Equivalences}}

%TC:ignore
\AgdaHide{
\begin{code}
module Setoids where
  open import Level using (_⊔_) renaming (suc to lsuc)
  open import Data.Nat hiding (_⊔_)
  open import Data.Nat.Properties.Simple
  open import Relation.Binary.Core using (Rel)
  open import Data.Product
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)
  open P.≡-Reasoning
\end{code}
}
%TC:endignore

A relation \AgdaDatatype{\_≈\_} is an equivalence if it is \emph{reflexive}, \emph{symmetric} and \emph{transitive}. The \AgdaDatatype{IsEquivalence} record bundles these three properties together:

%TC:ignore
\begin{code}
  record IsEquivalence  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    field
      refl   : ∀ {x} → x ≈ x
      sym    : ∀ {x y} → x ≈ y → y ≈ x
      trans  : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

    reflexive : ∀ {x y} → x ≡ y → x ≈ y
    reflexive P.refl = refl
\end{code}
%TC:endignore
Here, \AgdaFunction{reflexive} is not a field but a proof that is brought into scope when \AgdaDatatype{IsEquivalence} is opened. It shows that propositional equality \AgdaDatatype{\_≡\_} implies any other equivalence. In other words, \AgdaFunction{reflexive} shows that \AgdaDatatype{\_≡\_} is the smallest equivalence in Agda.

\subsection{Setoids}

A \emph{setoid} packages a type, called the \emph{carrier}, with a relation \AgdaDatatype{\_≈\_} defined on that type and a proof that this relation is an equivalence.

%TC:ignore
\begin{code}
  record Setoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
    field
      Carrier        : Set c
      _≈_            : Rel Carrier ℓ
      isEquivalence  : IsEquivalence _≈_
\end{code}
%TC:endignore
Setoids can be used to define quotients. For example, we could represent non-negative rational numbers as the setoid with carrier type \AgdaDatatype{ℕ} \AgdaDatatype{×} \AgdaDatatype{ℕ} and equivalence relation \AgdaDatatype{\_≈\_} defined as \AgdaBound{p} \AgdaInductiveConstructor{,} \AgdaBound{q} \AgdaDatatype{≈} \AgdaBound{p′} \AgdaInductiveConstructor{,} \AgdaBound{q′} if \AgdaBound{p} \AgdaFunction{*} \AgdaBound{q′} \AgdaDatatype{≡} \AgdaBound{p′} \AgdaFunction{*} \AgdaBound{q}. Here the quotient \AgdaDatatype{\_≈\_} partitions the domain \AgdaDatatype{ℕ} \AgdaDatatype{×} \AgdaDatatype{ℕ} into equivalence classes of pairs of natural numbers representing the same rational numbers.


\subsection{Equational reasoning\label{ssc:Equational-reasoning}}

Any setoid gives rise to a preorder, which consists of a carrier type and a relation with a reflexive and transitive law. This preorder can be used to do \emph{equational reasoning}, which provides syntactic sugar for applying the transitivity law. It aims to make Agda proofs look more like pen-and-paper proofs and will be used extensively in the next chapters.

As an example we take the setoid whose carrier is \AgdaDatatype{ℕ} with propositional equality \AgdaDatatype{\_≡\_} as the equivalence relation, and prove \AgdaSymbol{(}\AgdaBound{p} \AgdaFunction{*} \AgdaBound{q}\AgdaSymbol{)} \AgdaFunction{*} \AgdaBound{r} \AgdaDatatype{≡} \AgdaBound{q} \AgdaFunction{*} \AgdaSymbol{(}\AgdaBound{p} \AgdaFunction{*} \AgdaBound{r}\AgdaSymbol{)} in two different ways: first using transitivity explicitly, and then using equational reasoning.

The proofs assume that we have already shown that multiplication is commutative and associative, so the following are given:
\begin{align*}
\text{\AgdaFunction{*-comm}}\;&\AgdaSymbol{:}\;\text{\AgdaSymbol{(}\AgdaBound{m} \AgdaBound{n} \AgdaSymbol{:} ℕ\AgdaSymbol{)} \AgdaSymbol{→} \AgdaBound{m} \AgdaFunction{*} \AgdaBound{n} \AgdaDatatype{≡} \AgdaBound{n} \AgdaFunction{*} \AgdaBound{m}} \\
\text{\AgdaFunction{*-assoc}}\;&\AgdaSymbol{:}\;\text{(\AgdaBound{m} \AgdaBound{n} \AgdaBound{o} \AgdaSymbol{:} ℕ) \AgdaSymbol{→} (\AgdaBound{m} \AgdaFunction{*} \AgdaBound{n}) \AgdaFunction{*} \AgdaBound{o} \AgdaDatatype{≡} \AgdaBound{m} \AgdaFunction{*} (\AgdaBound{n} \AgdaFunction{*} \AgdaBound{o})}
\end{align*}
Additionally we have the transitivity law and congruence for binary functions, both parameterised over
\AgdaSymbol{∀} \AgdaSymbol{\{}\AgdaBound{a}\AgdaSymbol{\}} \AgdaSymbol{\{}\AgdaBound{A} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaBound{a}\AgdaSymbol{\}}:
\begin{align*}
\text{\AgdaFunction{P.trans}}\;&\AgdaSymbol{:}\;\text{\AgdaSymbol{\{}\AgdaBound{x} \AgdaBound{y} \AgdaBound{z} \AgdaSymbol{:} \AgdaBound{A}\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{y} \AgdaSymbol{→} \AgdaBound{y} \AgdaDatatype{≡} \AgdaBound{z} \AgdaSymbol{→} \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{z}} \\
\text{\AgdaFunction{P.cong₂}}\;&\AgdaSymbol{:}\;\text{\AgdaSymbol{\{}\AgdaBound{x} \AgdaBound{x′} \AgdaBound{y} \AgdaBound{y′} \AgdaSymbol{:} A\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{f} \AgdaSymbol{:} \AgdaBound{A} \AgdaSymbol{→} \AgdaBound{A} \AgdaSymbol{→} \AgdaBound{A}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{x′} \AgdaSymbol{→} \AgdaBound{y} \AgdaDatatype{≡} \AgdaBound{y′} \AgdaSymbol{→} \AgdaBound{f} \AgdaBound{x} \AgdaBound{y} \AgdaDatatype{≡} \AgdaBound{f} \AgdaBound{x′} \AgdaBound{y′}}
\end{align*}
The underlying reasoning is the same for both proofs: we first show \AgdaSymbol{(}\AgdaBound{p} \AgdaFunction{*} \AgdaBound{q}\AgdaSymbol{)} \AgdaFunction{*} \AgdaBound{r} \AgdaDatatype{≡} \AgdaSymbol{(}\AgdaBound{q} \AgdaFunction{*} \AgdaBound{p}\AgdaSymbol{)} \AgdaFunction{*} \AgdaBound{r}. It follows from \AgdaBound{p} \AgdaFunction{*} \AgdaBound{q} \AgdaDatatype{≡} \AgdaBound{q} \AgdaFunction{*} \AgdaBound{p} (by commutativity), \AgdaBound{r} \AgdaDatatype{≡} \AgdaBound{r} (by reflexivity) and congruence of \AgdaFunction{\_*\_}. Then we prove \AgdaSymbol{(}\AgdaBound{q} \AgdaFunction{*} \AgdaBound{p}\AgdaSymbol{)} \AgdaFunction{*} \AgdaBound{r} \AgdaDatatype{≡} \AgdaBound{q} \AgdaFunction{*} \AgdaSymbol{(}\AgdaBound{p} \AgdaFunction{*} \AgdaBound{r}\AgdaSymbol{)}, which is a direct consequence of the associativity rule. Using the lemmas specified above, the two steps can be written like this:
\begin{align*}
\text{\AgdaFunction{P.cong₂} \AgdaPrimitive{\_*\_} \AgdaSymbol{(}\AgdaFunction{*-comm} \AgdaBound{p} \AgdaBound{q}\AgdaSymbol{)} \AgdaInductiveConstructor{P.refl}}\;&\AgdaSymbol{:}\;\text{\AgdaSymbol{(}\AgdaBound{p} \AgdaFunction{*} \AgdaBound{q}\AgdaSymbol{)} \AgdaFunction{*} \AgdaBound{r} \AgdaDatatype{≡} \AgdaSymbol{(}\AgdaBound{q} \AgdaFunction{*} \AgdaBound{p}\AgdaSymbol{)} \AgdaFunction{*} \AgdaBound{r}} \\
\text{\AgdaFunction{*-assoc} \AgdaBound{q} \AgdaBound{p} \AgdaBound{r}}\;&\AgdaSymbol{:}\;\text{\AgdaSymbol{(}\AgdaBound{q} \AgdaFunction{*} \AgdaBound{p}\AgdaSymbol{)} \AgdaFunction{*} \AgdaBound{r} \AgdaDatatype{≡} \AgdaBound{q} \AgdaFunction{*} \AgdaSymbol{(}\AgdaBound{p} \AgdaFunction{*} \AgdaBound{r}\AgdaSymbol{)}}
\end{align*}
The initial equation is proved by transitivity which links the two steps together. Using normal function application syntax to apply transitivity, we get the following proof:

%TC:ignore
\begin{code}
  equiv₀ : (p q r : ℕ) → (p * q) * r ≡ q * (p * r)
  equiv₀ p q r = P.trans (P.cong₂ _*_ (*-comm p q) P.refl) (*-assoc q p r)
\end{code}
%TC:endignore
With equational reasoning it looks like this:

%TC:ignore
\begin{code}
  equiv₁ : (p q r : ℕ) → (p * q) * r ≡ q * (p * r)
  equiv₁ p q r =
    begin
      (p *  q) * r  ≡⟨ P.cong₂ _*_ (*-comm p q) P.refl ⟩
      (q *  p) * r  ≡⟨ *-assoc q p r ⟩
      q * (p  * r)
    ∎
\end{code}
%TC:endignore
The proof starts with \AgdaFunction{begin\_} followed by the left-hand side of the equivalence we are trying to prove. It ends with the right-hand side of the equivalence followed by \AgdaFunction{\_∎} (which is meant to resemble the \enquote{q.e.d.} symbol at the end of a proof). Intermediate steps are linked using \AgdaFunction{\_≡⟨\_⟩\_}; the term in angle brackets provides the justification. Transitivity is applied implicitly. Note that there is nothing special about \AgdaFunction{begin\_}, \AgdaFunction{\_≡⟨\_⟩\_} and \AgdaFunction{\_∎}---they are defined in the standard library like any other mixfix operator.

Which proof style one prefers is a matter of taste. Equational reasoning is more verbose---\AgdaFunction{equiv₁} spans seven lines compared to \AgdaFunction{equiv₀}'s two---but it makes intermediate steps explicit, which improves readability.

In general, we may choose an equivalence \AgdaDatatype{\_≈\_} other than propositional equality for our setoid. We can then freely mix steps using that equivalence relation \AgdaFunction{\_≈⟨\_⟩\_} and steps using propositional equality \AgdaFunction{\_≡⟨\_⟩\_} in an equational reasoning-style proof. Proving intermediate steps by propositional equality is allowed because by \AgdaFunction{reflexivity} (see \cref{ssc:Equivalences}), \AgdaBound{x}~\AgdaDatatype{≡}~\AgdaBound{y}~\AgdaSymbol{→} \AgdaBound{x}~\AgdaDatatype{≈}~\AgdaBound{y} for \emph{any} equivalence relation \AgdaDatatype{\_≈\_}.


\section{Algebra\label{sc:Algebra}}

In this Section, we review some properties binary operator might have, and define monoids, commutative monoids and semirings in terms of those properties.

\subsection{Properties of binary operators}

A binary operator \(\_\!\!⊗\!\!\_\) may have any of the following properties:

\begin{description}
\item[Associativity.] \((a ⊗ b) ⊗ c ≡ a ⊗ (b ⊗ c)\). The order in which subterms are evaluated has no bearing on the result. If an operator is known to be associative, terms consisting of multiple applications of that operator are usually written without parentheses: \((a ⊗ b) ⊗ c ≡ a ⊗ (b ⊗ c) ≡ a ⊗ b ⊗ c\).
In \AgdaModule{Algebra.FunctionProperties}, associativity of an operator \AgdaBound{\_∙\_} with respect to some relation \AgdaBound{\_≈\_} is defined as follows:

\begin{code}
  Associative : ∀ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) → (A → A → A) → Set _
  Associative _≈_ _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))
\end{code}

\item[Identity (or unit).] \(1 ⊗ a ≡ a\), \(a ⊗ 1 ≡ a\). Element \(1\) is called the left- or right-identity of \(\_\!\!⊗\!\!\_\) in the first and second equation, respectively.
In Agda's standard library, this property is encoded as a pair of predicates, \AgdaFunction{LeftIdentity} and \AgdaFunction{RightIdentity}:

%TC:ignore
\begin{code}
  LeftIdentity : ∀ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) → A → (A → A → A) → Set _
  LeftIdentity _≈_ e _∙_ = ∀ x → (e ∙ x) ≈ x

  RightIdentity : ∀ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) → A → (A → A → A) → Set _
  RightIdentity _≈_ e _∙_ = ∀ x → (x ∙ e) ≈ x
\end{code}
%TC:endignore
\AgdaDatatype{Identity} uses the non-dependent pair type \AgdaDatatype{\_×\_} to bundle the left- and right-identity laws together:

%TC:ignore
\begin{code}
  Identity : ∀ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) → A → (A → A → A) → Set _
  Identity _≈_ e ∙ = LeftIdentity _≈_ e ∙ × RightIdentity _≈_ e ∙
\end{code}
%TC:endignore

\item[Zero (or annihilator).] \(0 ⊗ a ≡ 0\), \(a ⊗ 0 ≡ 0\). The value \(0\) is the left- or right-identity of \(\_\!\!⊗\!\!\_\) in the first and second equation, respectively. This property is again encoded as pair of predicates in the same way as \AgdaFunction{Identity}. The left zero property is written as follows (\AgdaFunction{RightZero} is similar, and \AgdaFunction{Zero} is simply the pair of the two properties):

\begin{code}
  LeftZero : ∀ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) → A → (A → A → A) → Set _
  LeftZero _≈_ z _∙_ = ∀ x → (z ∙ x) ≈ z
\end{code}

\item[Commutativity.] \(a ⊗ b ≡ b ⊗ a\). Reordering operands does not change the result.
\begin{code}
  Commutative : ∀ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) → (A → A → A) → Set _
  Commutative _≈_ _∙_ = ∀ x y → (_∙_ x y) ≈ (_∙_ y x)
\end{code}
\end{description}
Binary operators may also interact in certain ways. If we add an operator \(\_\!\!⊕\!\!\_\), we may, for example, get a distributive property:

\begin{description}
\item[Distributivity.] \(a ⊗ (x ⊕ y) ≡ (a ⊗ x) ⊕ (a ⊗ y)\), \((x ⊕ y) ⊗ a ≡ (x ⊗ a) ⊕ (y ⊗ a)\). We say that \(\_\!\!⊗\!\!\_\) left- or right-distributes over \(\_\!\!⊕\!\!\_\), respectively. Left-distributivity is encoded in Agda as follows:

\begin{code}
  DistributesOverˡ :  ∀ {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) →
                      (A → A → A) → (A → A → A) → Set _
  DistributesOverˡ _≈_ _*_ _+_ =
    ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))
\end{code}
\end{description}

\subsection{Algebraic structures}

Certain combinations of the properties described in the previous subsection arise often, so for convenience, they are given names.

A \emph{semigroup} packages a carrier type together with an associative operation \(\_\!\!⊗\!\!\_\). If the operation has an identity \(ε\), the structure is called a \emph{monoid}. In a \emph{commutative monoid}, the operation is also commutative.
Given a monoid over \(\_\!\!⊗\!\!\_\) and a commutative monoid over \(\_\!\!⊕\!\!\_\), if the \(⊕\)-identity (this element is called \AgdaBound{0\#} in the standard library definition) is a zero for \(\_\!\!⊗\!\!\_\) and \(\_\!\!⊗\!\!\_\) distributes over \(\_\!\!⊕\!\!\_\) we call the composite structure a \emph{semiring}.

In the Agda standard library, the definitions of algebraic structures are split into two records, one containing the \emph{properties} and the other the \emph{data} of the structure.

\newpage

\begin{description}
\item[Semigroups.] The complete definition of a semigroup in Agda's standard library consists of the record types \AgdaDatatype{IsSemigroup} and \AgdaDatatype{Semigroup}:

%TC:ignore
\AgdaHide{
\begin{code}
module AlgebraicStructure where
  import Algebra.FunctionProperties as FunctionProperties
  open import Level
  open import Relation.Binary.Core
\end{code}
}

\begin{code}
  record IsSemigroup  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ)
                      (_∙_ : A → A → A) : Set (a ⊔ ℓ) where
    open FunctionProperties _≈_
    field
      isEquivalence  : IsEquivalence _≈_
      assoc          : Associative _∙_
      ∙-cong         : ∀ {x x′ y y′ : A} → x ≈ x′ → y ≈ y′ → (x ∙ y) ≈ (x′ ∙ y′)
\end{code}
%TC:endignore

\AgdaDatatype{IsSemigroup} encodes the properties of a semigroup. \AgdaBound{A} is the carrier type and \AgdaBound{\_≈\_} an equivalence relation over this type. The properties, associativity (the predicate \AgdaFunction{Associative} is defined in the previous Section) and congruence, are instantiated with respect to that equivalence relation.

%TC:ignore
\begin{code}
  record Semigroup c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier      : Set c
      _≈_          : Rel Carrier ℓ
      _∙_          : Carrier → Carrier → Carrier
      isSemigroup  : IsSemigroup _≈_ _∙_
\end{code}
%TC:endignore

The \AgdaDatatype{Semigroup} record packages a \AgdaField{Carrier} type, a relation \AgdaField{\_≈\_} and a binary operator \AgdaField{\_∙\_} together with the record containing the proofs that they satisfy the semigroup laws, \AgdaField{isSemigroup}.

\item[Monoids.] The definition of the \AgdaDatatype{Monoid} record contains a field \AgdaField{ε} in addition to those already present in \AgdaDatatype{Semigroup}. \AgdaDatatype{IsMonoid} contains two fields, \AgdaField{isSemigroup} \AgdaSymbol{:} \AgdaDatatype{IsSemigroup} \AgdaBound{≈} \AgdaBound{∙} and \AgdaField{identity} \AgdaSymbol{:} \AgdaDatatype{Identity} \AgdaBound{ε} \AgdaBound{∙}. That is, in addition to being a semigroup, the structure must have an identity element \(ε\).

\item[Commutative monoids.] \AgdaDatatype{CommutativeMonoid} contains the same data as \AgdaDatatype{Monoid}: an equivalence relation, an operator, and an identity. \AgdaDatatype{IsCommutativeMonoid}  extends \AgdaDatatype{IsSemigroup} in as similar way as \AgdaDatatype{IsMonoid} by adding an identity and a commutativity law.

\item[Semirings \enquote{without one}.] \AgdaDatatype{SemiringWithoutOne} is a structure almost like a semiring, except that it does not have a multiplicative identity.%
\footnote{We describe this structure, rather than the more commonly used semiring, because it is sufficient to show all the lemmas about big operators (see \cref{sc:Impl-Bigop-Props}) required for our proofs presented in \cref{ch:Semi} as well as \cref{ch:Gauss} and \cref{ch:Binom}. It was one goal of this project to always assume only what is really needed.} %
Its data contains \emph{two} binary operators \AgdaField{\_+\_} and \AgdaField{\_*\_} and a special element \AgdaField{0\#}.% which is simultaneously an identity for \AgdaField{\_+\_} and a zero for \AgdaField{\_*\_}. \AgdaDatatype{IsSemiringWithoutOne} specifies that \AgdaField{\_+\_} forms a commutative monoid with \AgdaField{0\#} as its identity elements, \AgdaField{\_*\_} forms a semigroup, \AgdaField{0\#} is a zero for \AgdaField{\_*\_} and \AgdaField{\_*\_} distributes over \AgdaField{\_+\_}.

\end{description}

% The Agda standard library defines algebraic structures in addition to the ones presented above. Because of its intended use in formalising algebraic path problems, the focus of this project was on semirings.

\chapter{Implementation\label{ch:Impl}}

In this Chapter we discuss the design and implementation of our big operator library.
We formalise four independent concepts: big operators as defined in \cref{sc:Conventions}, intervals of natural numbers, filters, and matrices. In combination, they allow for a large number of proofs involving big operators to be written in Agda. Taking apart the example from the introduction (\cref{eq:Intro-Example}), we will see how the expression
\[
\text{\AgdaSymbol{∀} \AgdaBound{n} \AgdaSymbol{→} \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…} \AgdaBound{n} \AgdaFunction{+} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{odd} \AgdaFunction{]} \AgdaBound{i} \AgdaDatatype{≡} \AgdaBound{n} \AgdaFunction{*} \AgdaBound{n}}
\] is assembled from the syntax definition for big operators (\AgdaFunction{Σ[\_←\_]\_}), intervals (\AgdaFunction{\_…\_}) and filters (\AgdaFunction{\_∥\_}):


\begin{description}
\item[Big operators.] The module \AgdaModule{Bigop.Core} defines an evaluation function and syntax for big operators. The submodules of \AgdaModule{Bigop.Properties} contain lemmas about big operators on different algebraic structures such as monoids and semirings.
\item[Intervals.] \AgdaModule{Bigop.Interval} contains functions for creating sequences of natural numbers and lemmas about those functions.
\item[Filters.] \AgdaModule{Bigop.Filter} defines a function which filters a list based on a decidable predicate. The directory of the same name contains syntax definitions that help write equational reasoning proofs with predicates (\AgdaModule{Bigop.Filter.PredicateReasoning}), definitions of the decidable predicates \AgdaDatatype{Even} and \AgdaDatatype{Odd} (\AgdaModule{Bigop.Filter.Predicates}) and general lemmas about filters (\AgdaModule{Bigop.Filter.Properties}).
\end{description}
In addition, a module formalising \textbf{matrices} has been written as part of this project, since this is one obvious area where the notation and lemmas written in this project can be used. It is completely independent from the rest of the source code.
For an overview of the directory structure and source code files, see \cref{fig:structure}.


\section{Design\label{sc:Design}}

Our goal in this project was to produce an Agda library for reasoning about big operators. We aimed to provide definitions and lemmas that abstracted over the particular operator being iterated. In several prototypes, we explored the design space for such a library. Two related questions had to be answered:

\begin{itemize}
\item What is the weakest algebraic structure that we can sensibly define a big operator on?
\item How should the domain of indices of a big operator be represented?
\end{itemize}

The representation of the index domain and the minimal requirements on the algebraic structure depend on each other: the weaker the structure of the domain representation, the stronger the algebra has to be and vice versa. For example, the difference between lists and multisets is that lists are ordered. But in order to compute the iterated big operator over a multiset, the elements of the carrier must be combined using the underlying binary operator in \emph{some} order, which in this case is arbitrary.

To get a well-defined result, the operator must consequently be immune to a re-ordering of its operands, in other words: removing the order from the domain adds commutativity to the properties required of the underlying operator.
In \cref{ssc:as-lists} and \cref{ssc:Monoid-structure} we argue that at least an identity and associativity law (that is, a monoid) is required, and that the appropriate index domain representation in this case is a list.

We built prototypes of alternative implementations, including a small finite sets library to represent the index domain (which added much complexity without tangible benefits) and an expression language for big operators---this idea may be worth reconsidering as part of an automated solver for big operator expressions (see \cref{sc:Future}). But for the use case of this library, representing a big operator by the result it evaluates to, and proving lemmas with respect to the underlying structure's equivalence relation turned out to be the best option (see \cref{ssc:Implementing}).

\section{Big operators\label{sc:Impl-Bigops}}


%TC:ignore
\AgdaHide{
\begin{code}
module BigOps where
  open import Level
  open import Algebra.Structures
  open import Relation.Binary.Core
\end{code}
%TC:endignore
}

In this Section, we will see how big operators are evaluated using the \AgdaModule{Bigop} module. We discuss why lists were chosen to represent indices, and why the binary operator must possess an identity and associativity law.


\subsection{Representing indices as lists\label{ssc:as-lists}}

Often in mathematical notation, the domain of a big operator expression is written using set notation. For this project, we decided to use lists instead for specifying the domain of a variable for the following reasons:

\begin{itemize}
\item Lists are \emph{ordered}. With unordered sets, the evaluation of big operators on non-commutative binary operators is not well-defined.

As an example, consider some arbitrary binary operator \(\_\!\!⊕\!\!\_\). Then \(\bigoplus_{i ∈ \{1,2\}} a_i\) could evaluate to either \(a_1 ⊕ a_2\) or \(a_2 ⊕ a_1\) since \(\{1,2\} = \{2,1\}\). But if \(\_⊕\_\) is non-commutative with \(a_1 ⊕ a_2 ≠ a_2 ⊕ a_1\), then the two results are not equal.

Using lists to specify the domain of \(i\), the problem evaporates: \(\bigoplus_{i ← [1,2]} a_i\) (note the square brackets indicating that the domain of indices is a list) evaluates to \(a_1 ⊕ a_2\) only, so the result of the big operator expression is well-defined.

\item Lists are well supported in Agda and commonly used: the standard library contains over 2000 lines of auxiliary definitions and lemmas about lists.
\end{itemize}

\subsection{Monoid structure\label{ssc:Monoid-structure}}

In this Subsection we argue that a binary operator used to build a well-defined big operator must at least possess an identity element and satisfy associativity.

\minisec{Identity}

The evaluation function for big operators, \AgdaFunction{fold} (defined in \cref{ssc:Implementing}), must be total like any other Agda function: it must accept any value in the domain of its argument types. For the list that the operator is being iterated over, one special value is \AgdaInductiveConstructor{[]}, the empty list.

What should a big operator iterated over an empty collection of indices evaluate to?
By convention, for any binary operator \(\_\!\!⊕\!\!\_\), \[\bigoplus_{i ← []} f(i) ⊕ x = x \qquad \text{and} \qquad x ⊕ \bigoplus_{i ← []} = x\] These two equations are exactly the left- and right-identity laws.

In order to simultaneously be able to compute any big operator over an list and enforce the intuition that it should behave as an identity, our library requires the binary operator to possess an identity element \(ε\). The evaluation of big operators is defined such that it returns \(ε\) when the collection of indices the big operator being evaluated on is empty: \[\bigoplus_{i ← []} f(i) = ε\]


\minisec{Associativity}

Assuming that \AgdaBound{i} ranges over some non-empty list of indices \(i_0, i_1, …, i_{n-1}, i_n\), the big operator expression \(\bigoplus_i f(i)\) is just an abbreviation for \[ f(i_0) ⊕ f(i_1) ⊕ ⋯ ⊕ f(i_{n-1}) ⊕ f(i_n) \]
Without any further information about \(\_\!⊕\!\_\), this string of symbols represents a \emph{family} of expressions due to the lack of parentheses. Two members of that family are the left and right fold over the index list with \(f\) applied to each element:
\begin{align*}
(⋯(f(i₀) ⊕ f(i₁)) ⋯ ⊕ f(i_{n-1})) ⊕ f(i_n) && \text{(left fold)} \\
f(i₀) ⊕ (f(i₁) ⊕ ⋯ (f(i_{n-1} ⊕ f(i_n)))⋯) && \text{(right fold)}
\end{align*}
The expression tree notation clearly shows the difference between the two folds (left fold on the left, right fold on the right):

\vspace{.15cm}
%\begin{figure}[hb]
%\begin{subfigure}[b]{.5\linewidth}
%  \begin{center}
\begin{minipage}{1\linewidth}
  \begin{minipage}{.5\linewidth}
    \centering
    \Tree [.\(⊕\) [ .\(⊕\) \edge[dashed]; [.\(⊕\) \(f(i₀)\) \(f(i₁)\) ] \(f(i_{n-1})\) ] \(f(i_n)\) ]
  \end{minipage}
  \begin{minipage}{.5\linewidth}
%  \end{center}
%  \label{fig:left-fold}
%  \caption{Left fold}
%\end{subfigure}
%\begin{subfigure}[b]{.5\linewidth}
%  \begin{center}
    \centering
    \Tree [.\(⊕\) \(f(i₀)\) [ .\(⊕\) \(f(i₁)\) \edge[dashed]; [.\(⊕\) \(f(i_{n-1})\) \(f(i_n)\) ] ] ]
  \end{minipage}
\end{minipage}
%  \end{center}
%  \label{fig:right-fold}
%  \caption{Right fold}
%\end{subfigure}
%\caption{Comparison between the expression trees representing a left fold \((((f(i₀) ⊕ f(i₁)) ⊕ ⋯) ⊕ f(i_{n-1})) ⊕ f(i_n)\) and a right fold \(f(i₀) ⊕ (f(i₁) ⊕ ⋯ (f(i_{n-1} ⊕ f(i_n))))\)}
%\label{fg:Folds}
%\end{figure}
\vspace{.1cm}
In order to actually compute the expression, we must decide on an order in which to add the terms. Unfortunately, the result of evaluating the left and right fold may differ. Our solution to this problem is to require \(\_\!\!⊕\!\!\_\) to be an associative operation:
in this case, all interpretations of the string of symbols representing the expanded big operator evaluate to the same value.
Note that this does not resolve the ambiguity of which expression tree the string represents---it just means that any expression tree in which all elements appear in the same left-to-right order compute the same value, and are therefore propositionally equal as terms (see \cref{ch:foldl-foldr} for a formal proof).


\subsection{Implementing big operators\label{ssc:Implementing}}

Recall from \cref{sc:Algebra} the definition of a monoid in Agda:

\begin{code}
  record Monoid c ℓ : Set (suc (c ⊔ ℓ)) where
    field
      Carrier   : Set c
      _≈_       : Rel Carrier ℓ
      _∙_       : Carrier → Carrier → Carrier
      ε         : Carrier
      isMonoid  : IsMonoid _≈_ _∙_ ε
\end{code}
The record \AgdaField{isMonoid} contains proofs that \AgdaField{\_≈\_} is an equivalence relation, \AgdaField{\_∙\_} is associative and congruent and \AgdaField{ε} is the identity for \AgdaField{\_∙\_} (all with respect to \AgdaField{\_≈\_}).
One core idea of this project is that any monoid exactly specifies a big operator (see \cref{ssc:Monoid-structure}) as follows:

\begin{itemize}
\item The binary operator \AgdaField{\_∙\_} gives us a way to combine elements of the monoid's carrier type. The associativity law guarantees that bracketing does not matter when we combine more than two elements. This means that left and right folds using \AgdaField{\_∙\_} are equivalent.
\item The identity element \AgdaField{ε} can be used as the result of a big operator expression over an empty index list. By the identity law, this makes any big operator expression over an empty index list behave as expected.
\end{itemize}

Given any monoid \AgdaBound{M}, we can bring its fields into scope:

%TC:ignore
\AgdaHide{
\begin{code}
  module Folds {c ℓ} (M : Monoid c ℓ) {i} {I : Set i} where
    open import Data.List using (List; foldr; map)
    open import Function using (_∘_)
\end{code}
}
\begin{code}
    open Monoid M
\end{code}
%TC:endignore
Using the carrier type, the monoid's binary operator and identity element, we can then define the function \AgdaFunction{crush} which reduces a list to an element of the carrier type using a fold over that list:\footnote{The name \AgdaFunction{crush} for this particular fold originated in \autocite{meertens_calculate_1996} and is combined in \autocite{gibbons_essence_2009} with a monoidal constraint.}

%TC:ignore
\begin{code}
    crush : List Carrier → Carrier
    crush = foldr _∙_ ε
\end{code}
%TC:endignore
\AgdaFunction{crush} \AgdaBound{xs} defined over \AgdaFunction{\_⊕\_} computes \(\bigoplus_{x ← xs} x\). The function itself is just an application of \AgdaFunction{foldr}, a right-fold over lists containing elements of the carrier type (as discussed in \cref{ssc:as-lists}, the choice of fold is arbitrary here since the operator is associative: we could just as well have defined \AgdaFunction{crush} in terms of the left-fold function \AgdaFunction{foldl}). \AgdaFunction{foldr} returns its second argument (\AgdaFunction{ε} in this case) if the list passed to it is empty; otherwise it combines the list elements using its first argument, a binary operator (\AgdaFunction{\_∙\_}). The type of \AgdaFunction{foldr} specialised to our use case is:
\[\text{\AgdaFunction{foldr}}\;\AgdaSymbol{:}\;\text{\AgdaSymbol{(}\AgdaBound{Carrier} \AgdaSymbol{→} \AgdaBound{Carrier} \AgdaSymbol{→} \AgdaBound{Carrier}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaBound{Carrier} \AgdaSymbol{→} \AgdaDatatype{List} \AgdaBound{Carrier} \AgdaSymbol{→} \AgdaBound{Carrier}}\]
We can now define the function \AgdaFunction{fold} which evaluates a big operator expression. It first applies a function \AgdaBound{f} \AgdaSymbol{:} \AgdaBound{I} \AgdaSymbol{→} \AgdaBound{Carrier} to each element of an index list using the function \AgdaFunction{map} defined in the standard library:
\[
\text{\AgdaFunction{map}}\;\AgdaSymbol{:}\;\text{\AgdaSymbol{(}\AgdaBound{I} \AgdaSymbol{→} \AgdaBound{Carrier}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{List} \AgdaBound{I} \AgdaSymbol{→} \AgdaDatatype{List} \AgdaBound{Carrier}}
\]
\AgdaFunction{fold} then applies \AgdaFunction{crush} to combine them into a single value of the monoid's carrier type.

%TC:ignore
\begin{code}
    fold : (I → Carrier) → List I → Carrier
    fold f = crush ∘ map f
\end{code}
%TC:endignore
The following syntax declaration should make the connection between this function and big operators clearer: \[
\text{\AgdaKeyword{syntax} \AgdaSymbol{fold} \AgdaSymbol{(λ} \AgdaSymbol{x} \AgdaSymbol{→} \AgdaSymbol{e)} \AgdaSymbol{v} \AgdaSymbol{=} \AgdaSymbol{Σ[} \AgdaSymbol{x} \AgdaSymbol{←} \AgdaSymbol{v} \AgdaSymbol{]} \AgdaSymbol{e}}
\]
It has the effect of rewriting any expression of the form \AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{e} into \AgdaFunction{fold} \AgdaSymbol{(}\AgdaSymbol{λ} \AgdaBound{x} \AgdaSymbol{→} \AgdaBound{e}\AgdaSymbol{)} \AgdaBound{xs}. Note that the \AgdaKeyword{syntax} keyword allows us to define new binding sites: the variable \AgdaBound{x} is \emph{bound} within the expression \AgdaBound{e}. This effect cannot be achieved with mixfix operators.

The following two examples show how \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{l} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i} evaluates. We first consider the case where \AgdaBound{l} \AgdaSymbol{=} \AgdaBound{l₀} \AgdaInductiveConstructor{∷} \AgdaBound{l₁} \AgdaInductiveConstructor{∷} \AgdaBound{l₂} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}:
\begin{align*}
\text{\AgdaFunction{fold} \AgdaFunction{f} \AgdaSymbol{(}\AgdaBound{l₀} \AgdaInductiveConstructor{∷} \AgdaBound{l₁} \AgdaInductiveConstructor{∷} \AgdaBound{l₂} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}\AgdaSymbol{)}}
\quad&\equiv\quad \text{\AgdaSymbol{(}\AgdaFunction{crush} \AgdaFunction{∘} \AgdaFunction{map} \AgdaFunction{f}\AgdaSymbol{)} \AgdaSymbol{(}\AgdaBound{l₀} \AgdaInductiveConstructor{∷} \AgdaBound{l₁} \AgdaInductiveConstructor{∷} \AgdaBound{l₂} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}\AgdaSymbol{)}} \\
\quad&\equiv\quad \text{\AgdaFunction{crush} \AgdaSymbol{(}\AgdaFunction{map} \AgdaFunction{f} \AgdaSymbol{(}\AgdaBound{l₀} \AgdaInductiveConstructor{∷} \AgdaBound{l₁} \AgdaInductiveConstructor{∷} \AgdaBound{l₂} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}\AgdaSymbol{)}\AgdaSymbol{)}} \\
\quad&\equiv\quad \text{\AgdaFunction{crush} \AgdaSymbol{(}\AgdaFunction{f} \AgdaBound{l₀} \AgdaInductiveConstructor{∷} \AgdaFunction{f} \AgdaBound{l₁} \AgdaInductiveConstructor{∷} \AgdaFunction{f} \AgdaBound{l₂} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}\AgdaSymbol{))}} \\
\quad&\equiv\quad \text{\AgdaFunction{f} \AgdaBound{l₀} \AgdaFunction{∙} \AgdaSymbol{(}\AgdaFunction{f} \AgdaBound{l₁} \AgdaFunction{∙} \AgdaSymbol{(}\AgdaFunction{f} \AgdaBound{l₂}\AgdaSymbol{))}} \\
\quad&\equiv\quad \text{\AgdaFunction{f} \AgdaBound{l₀} \AgdaFunction{∙} \AgdaFunction{f} \AgdaBound{l₁} \AgdaFunction{∙} \AgdaFunction{f} \AgdaBound{l₂}}
\end{align*}
In the last step, we are allowed to drop the parentheses because \AgdaFunction{\_∙\_} is associative by assumption. Next, we check what happens if \AgdaBound{l} is empty, that is, \AgdaBound{l} \AgdaSymbol{=} \AgdaInductiveConstructor{[]}:
\begin{align*}
\text{\AgdaFunction{fold} \AgdaFunction{f} \AgdaInductiveConstructor{[]}}
\quad&\equiv\quad \text{\AgdaSymbol{(}\AgdaFunction{crush} \AgdaFunction{∘} \AgdaFunction{map} \AgdaFunction{f}\AgdaSymbol{)} \AgdaInductiveConstructor{[]}} \\
\quad&\equiv\quad \text{\AgdaFunction{crush} \AgdaSymbol{(}\AgdaFunction{map} \AgdaFunction{f} \AgdaInductiveConstructor{[]}\AgdaSymbol{)}} \\
\quad&\equiv\quad \text{\AgdaFunction{crush} \AgdaInductiveConstructor{[]}} \\
\quad&\equiv\quad \text{\AgdaFunction{ε}}
\end{align*}


\section{Intervals\label{sc:Impl-Intervals}}

Intervals of natural numbers are commonly used as indices in big operator expressions. This Section describes how intervals are defined for two types introduced in \cref{ssc:Small}: natural numbers (\AgdaDatatype{ℕ}) and \AgdaDatatype{Fin}, which can be put into correspondence with some prefix of the natural numbers.

%TC:ignore
\AgdaHide{
\begin{code}
module Intervals where
  open import Data.List.Base
  open import Data.Fin using (Fin; fromℕ≤)
  open import Data.Nat.Base
  open import Data.Nat.Properties using (m≤m+n)
  open import Data.Nat.Properties.Simple using (+-suc)
\end{code}
%TC:endignore
}

Defining intervals of type \AgdaDatatype{ℕ} is straightforward. The module \AgdaModule{Bigop.Interval.Nat} consists of the following four definitions:

%TC:ignore
\begin{code}
  upFrom : ℕ → ℕ → List ℕ
  upFrom from zero       = []
  upFrom from (suc len)  = from ∷ upFrom (suc from) len

  range : ℕ → ℕ → List ℕ
  range m n = upFrom m (n ∸ m)

  _…<_ = range

  _…_ : ℕ → ℕ → List ℕ
  m … n = range m (suc n)
\end{code}
%TC:endignore
\AgdaFunction{upFrom} \AgdaBound{m} \AgdaBound{n} evaluates to the interval containing \AgdaBound{n} consecutive natural numbers, starting with \AgdaBound{m}. \AgdaFunction{range} returns a list of natural numbers starting with \AgdaBound{m} up to but not including \AgdaBound{n}. In case \(n ≤ m\), \AgdaFunction{range} returns the empty list.

The infix operator \AgdaFunction{\_…<\_} is just a synonym for \AgdaFunction{range}. The notation is meant to make it clear that the interval does not include the upper bound. On the other hand, \AgdaFunction{\_…\_} explicitly includes the upper bound, so it defines a closed interval.

\AgdaModule{Bigop.Interval.Fin} contains four definitions with the same names as the module presented above. Their types are:
\begin{align*}
\text{\AgdaFunction{upFrom}}\;&\AgdaSymbol{:}\;\text{\AgdaSymbol{(}\AgdaBound{from} \AgdaBound{len} \AgdaSymbol{:} \AgdaDatatype{ℕ}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{List} \AgdaSymbol{(}\AgdaDatatype{Fin} \AgdaSymbol{(}\AgdaBound{from} \AgdaFunction{+} \AgdaBound{len}\AgdaSymbol{)}\AgdaSymbol{)}} \\
\text{\AgdaFunction{range}}\;\text{\AgdaFunction{\_…<\_}}\;&\AgdaSymbol{:}\;\text{\AgdaDatatype{ℕ} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{to} \AgdaSymbol{:} \AgdaDatatype{ℕ}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{List} \AgdaSymbol{(}\AgdaDatatype{Fin} \AgdaBound{to}\AgdaSymbol{)}} \\
\text{\AgdaFunction{\_…\_}}\;&\AgdaSymbol{:}\;\text{\AgdaDatatype{ℕ} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{to} \AgdaSymbol{:} \AgdaDatatype{ℕ}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{List} \AgdaSymbol{(}\AgdaDatatype{Fin} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{to}\AgdaSymbol{)}\AgdaSymbol{)}}
\end{align*}
We omit the definitions of those functions here. They are more involved than the corresponding definitions presented above because we need to convert from \AgdaDatatype{ℕ} to \AgdaDatatype{Fin} and rewrite types to make the inductive definitions work.

Since \AgdaDatatype{Fin} \AgdaBound{n} is the type of natural numbers less than \AgdaBound{n}, we can tell from the types of the functions that their upper bounds are as expected.

\section{Filters\label{sc:Impl-Filters}}

Sometimes it is useful to write the list of indices of a big operator expression as an interval out of which we only keep those indices which fulfill a certain property. The odd Gauss equation, for example, has as its right-hand side \enquote{the sum of all \emph{odd} numbers from zero to \(2n\)}. In order to express such an equation in this framework, we need a way to filter out the even numbers. In this Section, we will define filters using a infix operator that combines well with the syntax for big operators presented in \cref{ssc:Implementing}. Note that although the filter module was implemented as part of our big operators library, it does not depend on big operators or intervals, and could in the future be spun off into a separate library.

%TC:ignore
\AgdaHide{
\begin{code}
module Filters where
  open import Data.List.Base
  open import Function using (_∘_)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Relation.Unary
  open import Relation.Binary.PropositionalEquality
\end{code}
}
%TC:endignore

The filter operator \AgdaFunction{\_∥\_} takes a list and a decidable predicate over the list's element type, and returns the list containing only those elements of the input list which satisfy that predicate. Its definition is a straightforward inductive definition, with a case split on whether the predicate is satisfied: if \AgdaInductiveConstructor{yes}, then the element is included in the result; otherwise it is dropped:

%TC:ignore
\begin{code}
  _∥_ : ∀ {a p} {A : Set a} {P : Pred A p} → List A → Decidable P → List A
  []        ∥ dec = []
  (x ∷ xs)  ∥ dec with dec x
  (x ∷ xs)  ∥ dec | yes  _ = x ∷ (xs ∥ dec)
  (x ∷ xs)  ∥ dec | no   _ = xs ∥ dec
\end{code}
%TC:endignore
Any decidable predicate can be converted into a function from the predicate's domain to \AgdaDatatype{Bool}, mapping \AgdaInductiveConstructor{yes} to \AgdaInductiveConstructor{true} and \AgdaInductiveConstructor{no} to \AgdaInductiveConstructor{false} and dropping the evidence. This function is called \AgdaFunction{⌊\_⌋} in the Agda standard library. \AgdaFunction{⌊\_⌋} \AgdaFunction{∘} \AgdaFunction{dec} \AgdaSymbol{:} \AgdaBound{A} \AgdaSymbol{→} \AgdaDatatype{Bool} can then be passed to the function \AgdaFunction{filter}, also defined in the standard library, which filters a list using a function from the list's element type to \AgdaDatatype{Bool}:
\[ \text{\AgdaFunction{filter}}\;\AgdaSymbol{:}\;\text{\AgdaSymbol{∀} \AgdaSymbol{\{}\AgdaBound{a}\AgdaSymbol{\}} \AgdaSymbol{\{}\AgdaBound{A} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaBound{a}\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{A} \AgdaSymbol{→} \AgdaDatatype{Bool}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaDatatype{List} \AgdaBound{A} \AgdaSymbol{→} \AgdaDatatype{List} \AgdaBound{A}} \]
The following proof shows that the result of filtering a list using \AgdaFunction{\_∥\_} is equal to calling \AgdaFunction{filter} with the converted decidable predicate as its first argument:

%TC:ignore
\begin{code}
  ∥-filters :  ∀ {a p} {A : Set a} {P : Pred A p} (xs : List A) (dec : Decidable P) →
               xs ∥ dec ≡ filter (⌊_⌋ ∘ dec) xs
  ∥-filters []        dec = refl
  ∥-filters (x ∷ xs)  dec with dec x
  ∥-filters (x ∷ xs)  dec | yes  _ = cong (_∷_ x) (∥-filters xs dec)
  ∥-filters (x ∷ xs)  dec | no   _ = ∥-filters xs dec
\end{code}
%TC:endignore
\AgdaModule{Bigop.Filter} also defines the following important utility function \AgdaFunction{∁′}, which takes a decidable predicate and returns its complement. For any \AgdaBound{x} in the domain of predicate \AgdaBound{P}, if \AgdaBound{x} satisfies \AgdaBound{P}, it returns evidence that \AgdaBound{x} does not satisfy the complement of \AgdaBound{P}, written \AgdaFunction{∁} \AgdaBound{P}, and vice versa:

%TC:ignore
\begin{code}
  ∁′ : ∀ {i p} {I : Set i} {P : Pred I p} → Decidable P → Decidable (∁ P)
  ∁′ p x with p x
  ∁′ p x | yes q  = no (λ ¬q → ¬q q)
  ∁′ p x | no ¬q  = yes (λ q → ¬q q)
\end{code}
%TC:endignore
In \AgdaModule{Bigop.Filter.Properties}, we show a number of lemmas about filters and decidable properties defined in this way. In each of them, we pick an element from the list and examine whether it satisfies the predicate. They can be considered variants of list induction. In some proofs it is more convenient to perform induction on the list of indices from the head (the first element of the list). This can be achieved simply by pattern matching on a non-empty list using the constructor \AgdaInductiveConstructor{\_∷\_}. In other proofs we may want to start with the last element. The function \AgdaBound{xs} \AgdaFunction{∷ʳ} \AgdaBound{x} abbreviates \AgdaBound{xs} \AgdaInductiveConstructor{∷} \AgdaBound{x} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}, and allows us to split a list into its last element (\AgdaBound{x}) and everything preceding it (\AgdaBound{xs}).

Omitting the parameters
\AgdaSymbol{\{}\AgdaBound{i} \AgdaBound{ℓ} \AgdaSymbol{:} \AgdaDatatype{Level}\AgdaSymbol{\}} \AgdaSymbol{\{}\AgdaBound{I} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaBound{i}\AgdaSymbol{\}} \AgdaSymbol{\{}\AgdaBound{P} \AgdaSymbol{:} \AgdaDatatype{Pred} \AgdaBound{I} \AgdaBound{ℓ}\AgdaSymbol{\}} \AgdaBound{x} \AgdaBound{xs} \AgdaSymbol{(}\AgdaBound{p} \AgdaSymbol{:} \AgdaDatatype{Decidable} \AgdaBound{P}\AgdaSymbol{)}, the types of the filter lemmas are as follows:
\begin{align*}
\text{\AgdaFunction{head-yes}}\;&\AgdaSymbol{:}\;
\text{\AgdaBound{P} \AgdaBound{x} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{x} \AgdaInductiveConstructor{∷} \AgdaBound{xs}\AgdaSymbol{)} \AgdaFunction{∥} \AgdaBound{p} \AgdaDatatype{≡} \AgdaBound{x} \AgdaInductiveConstructor{∷} \AgdaSymbol{(}\AgdaBound{xs} \AgdaFunction{∥} \AgdaBound{p}\AgdaSymbol{)}} \\
%
\text{\AgdaFunction{last-yes}}\;&\AgdaSymbol{:}\;
\text{\AgdaBound{P} \AgdaBound{x} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{xs} \AgdaFunction{∷ʳ} \AgdaBound{x}\AgdaSymbol{)} \AgdaFunction{∥} \AgdaBound{p} \AgdaDatatype{≡} \AgdaSymbol{(}\AgdaBound{xs} \AgdaFunction{∥} \AgdaBound{p}\AgdaSymbol{)} \AgdaFunction{∷ʳ} \AgdaBound{x}} \\
%
\text{\AgdaFunction{head-no}}\;&\AgdaSymbol{:}\;
\text{\AgdaFunction{¬} \AgdaBound{P} \AgdaBound{x} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{x} \AgdaInductiveConstructor{∷} \AgdaBound{xs}\AgdaSymbol{)} \AgdaFunction{∥} \AgdaBound{p} \AgdaDatatype{≡} \AgdaBound{xs} \AgdaFunction{∥} \AgdaBound{p}} \\
%
\text{\AgdaFunction{last-no}}\;&\AgdaSymbol{:}\;
\text{\AgdaFunction{¬} \AgdaBound{P} \AgdaBound{x} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{xs} \AgdaFunction{∷ʳ} \AgdaBound{x}\AgdaSymbol{)} \AgdaFunction{∥} \AgdaBound{p} \AgdaDatatype{≡} \AgdaBound{xs} \AgdaFunction{∥} \AgdaBound{p}} \\
%
\text{\AgdaFunction{head-∁-yes}}\;&\AgdaSymbol{:}\;
\text{\AgdaBound{P} \AgdaBound{x} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{x} \AgdaInductiveConstructor{∷} \AgdaBound{xs}\AgdaSymbol{)} \AgdaFunction{∥} \AgdaFunction{∁′} \AgdaBound{p} \AgdaDatatype{≡} \AgdaBound{xs} \AgdaFunction{∥} \AgdaFunction{∁′} \AgdaBound{p}} \\
%
\text{\AgdaFunction{head-∁-no}}\;&\AgdaSymbol{:}\;
\text{\AgdaFunction{¬} \AgdaBound{P} \AgdaBound{x} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{x} \AgdaInductiveConstructor{∷} \AgdaBound{xs}\AgdaSymbol{)} \AgdaFunction{∥} \AgdaFunction{∁′} \AgdaBound{p} \AgdaDatatype{≡} \AgdaBound{x} \AgdaInductiveConstructor{∷} \AgdaSymbol{(}\AgdaBound{xs} \AgdaFunction{∥} \AgdaFunction{∁′} \AgdaBound{p}\AgdaSymbol{)}}
\end{align*}
All six of the above are proved using the following more general lemmas (all of which take the implicit parameters \AgdaSymbol{\{}\AgdaBound{i} \AgdaBound{ℓ} \AgdaSymbol{:} \AgdaDatatype{Level}\AgdaSymbol{\}} \AgdaSymbol{\{}\AgdaBound{I} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaBound{i}\AgdaSymbol{\}} \AgdaSymbol{\{}\AgdaBound{P} \AgdaSymbol{:} \AgdaDatatype{Pred} \AgdaBound{I} \AgdaBound{ℓ}\AgdaSymbol{\}}):
\begin{align*}
\text{\AgdaFunction{∥-distrib}}\;&\AgdaSymbol{:}\;\text{\AgdaSymbol{∀} \AgdaBound{xs} \AgdaBound{ys} \AgdaSymbol{(}\AgdaBound{p} \AgdaSymbol{:} \AgdaDatatype{Decidable} \AgdaBound{P}\AgdaSymbol{)} \AgdaSymbol{→} (\AgdaBound{xs} \AgdaFunction{++} \AgdaBound{ys}\AgdaSymbol{)} \AgdaFunction{∥} \AgdaBound{p} \AgdaDatatype{≡} (\AgdaBound{xs} \AgdaFunction{∥} \AgdaBound{p}\AgdaSymbol{)} \AgdaFunction{++} (\AgdaBound{ys} \AgdaFunction{∥} \AgdaBound{p}\AgdaSymbol{)}} \\
\text{\AgdaFunction{∥-step-yes}}\;&\AgdaSymbol{:}\;\text{\AgdaSymbol{∀} \AgdaBound{x} \AgdaSymbol{(}\AgdaBound{p} \AgdaSymbol{:} \AgdaDatatype{Decidable} \AgdaBound{P}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaBound{P} \AgdaBound{x} \AgdaSymbol{→} \AgdaFunction{[} \AgdaBound{x} \AgdaFunction{]} \AgdaFunction{∥} \AgdaBound{p} \AgdaDatatype{≡} \AgdaFunction{[} \AgdaBound{x} \AgdaFunction{]}} \\
\text{\AgdaFunction{∥-step-no}}\;&\AgdaSymbol{:}\;\text{\AgdaSymbol{∀} \AgdaBound{x} \AgdaSymbol{(}\AgdaBound{p} \AgdaSymbol{:} \AgdaDatatype{Decidable} \AgdaBound{P}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaFunction{¬} \AgdaBound{P} \AgdaBound{x} \AgdaSymbol{→} \AgdaFunction{[} \AgdaBound{x} \AgdaFunction{]} \AgdaFunction{∥} \AgdaBound{p} \AgdaDatatype{≡} \AgdaInductiveConstructor{[]}} \\
\end{align*}
In addition, we prove \AgdaFunction{ordinals-filter} (see its type below). It states that the interval of length \AgdaBound{n} starting at \AgdaBound{m} contains the number \AgdaBound{k} exactly once, provided that \AgdaBound{m} \AgdaDatatype{≤} \AgdaBound{k} and \AgdaBound{k} \AgdaDatatype{<} \AgdaBound{m} \AgdaFunction{+} \AgdaBound{n}. \enquote{Containing \AgdaBound{k} exactly once} is expressed in terms of filtering by the decidable predicate \AgdaFunction{≟N} \AgdaBound{k}, which holds only for natural numbers equal to \AgdaBound{k}. If the result of applying this filter to an interval yields a singleton list containing only \AgdaBound{k}, then \AgdaBound{k} must have appeared exactly once in the interval.
\[ \text{\AgdaFunction{ordinals-filter} \AgdaSymbol{:} \AgdaSymbol{∀} \AgdaBound{m} \AgdaBound{n} \AgdaBound{k} \AgdaSymbol{→} \AgdaBound{m} \AgdaDatatype{≤} \AgdaBound{k} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{k<m+n} \AgdaSymbol{:} \AgdaBound{k} \AgdaDatatype{<} \AgdaBound{m} \AgdaFunction{+} \AgdaBound{n}\AgdaSymbol{)} \AgdaSymbol{→}
                  \AgdaFunction{upFrom} \AgdaBound{m} \AgdaBound{n} \AgdaFunction{∥} \AgdaSymbol{(}\AgdaFunction{≟N} \AgdaBound{k}\AgdaSymbol{)} \AgdaDatatype{≡} \AgdaBound{k} \AgdaInductiveConstructor{∷} \AgdaInductiveConstructor{[]}} \]
This lemma is used in the proof that the identity matrix really is the identity element of the semiring of square matrices (see \cref{Semi-Times}).


\section{Properties of big operators\label{sc:Impl-Bigop-Props}}

In this Section, we discuss how the properties of the underlying operators \AgdaFunction{\_+\_} and \AgdaFunction{\_*\_} determine the properties of their induced big operators.

The lemmas in this section reside in \AgdaModule{Bigop.Properties}. They are intended to be used as follows: assuming we have some commutative monoid \AgdaBound{CM} \AgdaSymbol{:} \AgdaDatatype{CommutativeMonoid}. Then the following line will bring the lemmas concerning commutative monoids into scope under the module name \AgdaModule{Σ}:
\[
\text{\AgdaKeyword{module} \AgdaModule{Σ} \AgdaSymbol{=} \AgdaModule{Bigop.Properties.CommutativeMonoid} \AgdaBound{CM}}
\]
For convenience, \AgdaModule{Bigop.Properties.CommutativeMonoid} re-exports all lemmas about monoids and \AgdaModule{Bigop.Properties.SemiringWithoutOne} re-exports the commutative monoid lemmas.


\subsection{Monoid lemmas\label{ssc:Monoid-lemmas}}

Monoids are endowed with an identity and an associativity law. Based on these two properties, there are a few things we can say about what happens when a big operator is defined on a monoid.

\begin{description}
\item[Lifted identity.]
The identity law can be lifted to give the following equivalence for the monoid's big operator:
\[
\text{(\AgdaFunction{identity})}\qquad\text{\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{is} \AgdaFunction{]} \AgdaFunction{ε} \AgdaDatatype{≈} \AgdaFunction{ε}}
\]

\item[Distributivity over \AgdaFunction{\_++\_}.]
It follows from the monoid associativity law that big operators distribute over the list append function \AgdaFunction{\_++\_} as follows:
\[\text{(\AgdaFunction{join})}\qquad\text{
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i} \AgdaFunction{+} \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{ys} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{++} \AgdaBound{ys} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i}
}\]

\item[Congruence.] Given \AgdaBound{xs} \AgdaDatatype{≡} \AgdaBound{ys} and \AgdaSymbol{∀} \AgdaBound{x} \AgdaSymbol{→} \AgdaBound{f} \AgdaBound{x} \AgdaDatatype{≈} \AgdaBound{g} \AgdaBound{x}, we can show that
\[
\text{(\AgdaFunction{cong})}\qquad\text{\AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{y} \AgdaFunction{←} \AgdaBound{ys} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{y}}
\]

\end{description}

\subsection{Commutative monoid lemmas}

If the binary operation \AgdaFunction{\_+\_} is commutative as well as associative, the big operator defined on it has more properties that we can use in proofs.

\begin{description}
\item[Distributivity over \AgdaFunction{\_+\_}.] Combining associativity and distributivity of \AgdaFunction{\_+\_}, we can show that big operators distribute as follows:
\[
\text{(\AgdaFunction{merge})}\qquad\text{\AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x} \AgdaFunction{+} \AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{g} \AgdaBound{x} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x} \AgdaFunction{+} \AgdaBound{g} \AgdaBound{x}}
\]

\item[Swapping big operators.] If the underlying operator \AgdaFunction{\_+\_} is commutative, the order in which big operators are evaluated does not matter:
\[
\text{(\AgdaFunction{swap})}\qquad\text{\AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaSymbol{(}\AgdaFunction{Σ[} \AgdaBound{y} \AgdaFunction{←} \AgdaBound{ys} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x} \AgdaBound{y}\AgdaSymbol{)} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{y} \AgdaFunction{←} \AgdaBound{ys} \AgdaFunction{]} \AgdaSymbol{(}\AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x} \AgdaBound{y}\AgdaSymbol{)}}
\]

\item[Splitting by a predicate.] Any list can be split into two lists, one containing those elements which satisfy a decidable predicate (\AgdaBound{xs} \AgdaFunction{∥} \AgdaBound{dec}) and one containing those which do not (\AgdaBound{xs} \AgdaFunction{∥} \AgdaFunction{∁′} \AgdaBound{dec}). Assuming commutativity, we can split the index list of a big operator expression using any decidable predicate and add them together to get the same result as taking the sum over the original list:
\[
\text{(\AgdaFunction{split-P})}\qquad
\text{\AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{∥} \AgdaBound{dec} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x} \AgdaFunction{+} \AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{∥} \AgdaFunction{∁′} \AgdaBound{dec} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x}}
\]

\end{description}


\subsection{\enquote{Semiring without one} lemmas}

A \enquote{semiring without one} consists of a commutative monoid over an operation \AgdaFunction{\_+\_} and a semigroup over an operation \AgdaFunction{\_*\_} with a zero element (annihilator). Additionally, \AgdaFunction{\_*\_} distributes over \AgdaFunction{\_+\_}. This allows us to prove two distributivity laws:
\begin{align*}
\text{(\AgdaFunction{distrˡ})}\qquad
&\text{\AgdaBound{a} \AgdaFunction{*} \AgdaSymbol{(}\AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x}\AgdaSymbol{)} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{a} \AgdaFunction{*} \AgdaBound{f} \AgdaBound{x}} \\
\text{(\AgdaFunction{distrʳ})}\qquad
&\text{\AgdaSymbol{(}\AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x}\AgdaSymbol{)} \AgdaFunction{*} \AgdaBound{a} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x} \AgdaFunction{*} \AgdaBound{a}}
\end{align*}

\subsection{Boolean algebra lemmas}

The lemmas about big operators on monoids, commutative monoids and semirings presented above were directly relevant to the theorems we aimed to prove (see \cref{ch:Semi} as well as \cref{ch:Gauss} and \cref{ch:Binom}). To demonstrate that our approach scales to more complex algebraic structures, we proved the big operator version of the de Morgan laws for arbitrary Boolean algebras. Two examples of Boolean algebras are: Booleans with the two operators logical \emph{and} and logical \emph{or}, and sets with intersection and union.

In order to make the propositions and proofs more readable, we added two syntax definitions as synonyms for \AgdaFunction{fold} (see \cref{sc:Impl-Bigops}):
\begin{gather*}
\text{\AgdaKeyword{syntax} \AgdaSymbol{fold} \AgdaSymbol{(λ} \AgdaSymbol{x} \AgdaSymbol{→} \AgdaSymbol{e)} \AgdaSymbol{v} \AgdaSymbol{=} \AgdaSymbol{⋁[} \AgdaSymbol{x} \AgdaSymbol{←} \AgdaSymbol{v} \AgdaSymbol{]} \AgdaSymbol{e}} \\
\text{\AgdaKeyword{syntax} \AgdaSymbol{fold} \AgdaSymbol{(λ} \AgdaSymbol{x} \AgdaSymbol{→} \AgdaSymbol{e)} \AgdaSymbol{v} \AgdaSymbol{=} \AgdaSymbol{⋀[} \AgdaSymbol{x} \AgdaSymbol{←} \AgdaSymbol{v} \AgdaSymbol{]} \AgdaSymbol{e}}
\end{gather*}
Using this notation, we proved that for any Boolean algebra the following variants of the de Morgan laws hold:
\begin{align*}
\text{(\AgdaFunction{deMorgan₁})}\qquad&\text{%\AgdaSymbol{∀} \AgdaSymbol{\{}\AgdaBound{i}\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaSymbol{\{}\AgdaBound{I} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaBound{i}\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{f} \AgdaSymbol{:} \AgdaBound{I} \AgdaSymbol{→} \AgdaBound{R}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{xs} \AgdaSymbol{:} \AgdaDatatype{List} \AgdaBound{I}\AgdaSymbol{)} \AgdaSymbol{→}%
            \AgdaFunction{¬} \AgdaSymbol{(}\AgdaFunction{⋀[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i}\AgdaSymbol{)} \AgdaDatatype{≈} \AgdaFunction{⋁[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaFunction{¬} \AgdaBound{f} \AgdaBound{x}} \\
\text{(\AgdaFunction{deMorgan₂})}\qquad&\text{%\AgdaSymbol{∀} \AgdaSymbol{\{}\AgdaBound{i}\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaSymbol{\{}\AgdaBound{I} \AgdaSymbol{:} \AgdaPrimitiveType{Set} \AgdaBound{i}\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{f} \AgdaSymbol{:} \AgdaBound{I} \AgdaSymbol{→} \AgdaBound{R}\AgdaSymbol{)} \AgdaSymbol{→} \AgdaSymbol{(}\AgdaBound{xs} \AgdaSymbol{:} \AgdaDatatype{List} \AgdaBound{I}\AgdaSymbol{)} \AgdaSymbol{→}%
            \AgdaFunction{¬} \AgdaSymbol{(}\AgdaFunction{⋁[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{x}\AgdaSymbol{)} \AgdaDatatype{≈} \AgdaFunction{⋀[} \AgdaBound{x} \AgdaFunction{←} \AgdaBound{xs} \AgdaFunction{]} \AgdaFunction{¬} \AgdaBound{f} \AgdaBound{i}}
\end{align*}
Boolean algebras provide a rich structure, and more interesting properties of this structure could be lifted into lemmas about their big operators. The point here is just to demonstrate that the framework we developed is very general, for example allowing us to write proofs concerning the interaction between two big operators defined on the same algebraic structure.

\section{\label{sc:Impl-Matrices}Matrices}

In order to prove that square matrices over semirings are again semirings, it was necessary to formalise matrices first (the Agda standard library currently lacks a matrix library). This module is independent from the rest of the project.

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
Next we define a relation between matrices based on a relation between their elements:

%TC:ignore
\begin{code}
  Pointwise :  ∀ {s t ℓ} {S : Set s} {T : Set t} (_∼_ : REL S T ℓ)
               {m n} → Matrix S m n → Matrix T m n → Set ℓ
  Pointwise _~_ A B = ∀ r c → A [ r , c ] ~ B [ r , c ]
\end{code}
%TC:endignore
The intuition for this definition is this: in order to show that the \AgdaDatatype{Pointwise} \AgdaDatatype{\_\sim\_} relation holds between two matrices, we must give a function which, for any row index \AgdaBound{r} and any column index \AgdaBound{c}, produces evidence that the relation \AgdaDatatype{\_\sim\_} holds between the elements of the two matrices at this point.

We would like to use \AgdaDatatype{Pointwise} \AgdaBound{\_∼\_} as an equivalence relation in proofs. \AgdaFunction{PW-isEquivalence} shows that if \AgdaBound{\_~\_} is an equivalence relation, then so is its pointwise lifting:

%TC:ignore
\begin{code}
  PW-isEquivalence :  ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} {m n} →
                      IsEquivalence _≈_ → IsEquivalence (Pointwise _≈_ {m = m} {n})
  PW-isEquivalence {_≈_ = ≈} eq = record
    { refl = PW-refl
    ; sym = PW-sym
    ; trans = PW-trans
    }
    where
      open IsEquivalence eq

      ≋ = Pointwise ≈

      PW-refl : Reflexive ≋
      PW-refl = (λ r c → refl)

      PW-sym : Symmetric ≋
      PW-sym eq = (λ r c → sym (eq r c))

      PW-trans : Transitive ≋
      PW-trans eq₁ eq₂ = (λ r c → trans (eq₁ r c) (eq₂ r c))
\end{code}
%TC:endignore
Let us consider \AgdaFunction{PW-sym} in more detail. The property \AgdaFunction{Symmetric} \AgdaDatatype{≋} is defined as \AgdaSymbol{∀}~\AgdaSymbol{\{}\AgdaBound{A} \AgdaBound{B}\AgdaSymbol{\}} \AgdaSymbol{→} \AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{B} \AgdaSymbol{→} \AgdaBound{B} \AgdaDatatype{≋} \AgdaBound{A}. That is, it transforms evidence of \AgdaBound{eq} \AgdaSymbol{:} \AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{B} into evidence that \AgdaBound{B} \AgdaDatatype{≋} \AgdaBound{A}, which is just a synonym for \AgdaSymbol{∀} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaBound{B} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≈} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}.
In order to construct a function of this type, we abstract over \AgdaBound{r} and \AgdaBound{c} and then apply the symmetry law of the underlying equivalence \AgdaFunction{sym} to \AgdaBound{eq} \AgdaBound{r} \AgdaBound{c} like so:
\begin{align*}
\text{\AgdaSymbol{λ} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaBound{eq} \AgdaBound{r} \AgdaBound{c}}
  &\;\AgdaSymbol{:}\; \text{\AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{B}} \\
  &\;\AgdaSymbol{:}\; \text{\AgdaSymbol{∀} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≈} \AgdaBound{B} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}} \\
\text{\AgdaSymbol{λ} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaFunction{sym} \AgdaSymbol{(}\AgdaBound{eq} \AgdaBound{r} \AgdaBound{c}\AgdaSymbol{)}}
  &\;\AgdaSymbol{:}\; \text{\AgdaSymbol{∀} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaBound{B} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≈} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}} \\
  &\;\AgdaSymbol{:}\; \text{\AgdaBound{B} \AgdaDatatype{≋} \AgdaBound{A}} \\
\end{align*}
Our symmetry proof for \AgdaDatatype{\_≋\_} is thus

\[\text{
\AgdaFunction{≋-sym} \AgdaBound{eq} \AgdaSymbol{=} \AgdaSymbol{λ} \AgdaBound{r} \AgdaBound{c} \AgdaSymbol{→} \AgdaFunction{sym} \AgdaSymbol{(}\AgdaBound{eq} \AgdaBound{r} \AgdaBound{c}\AgdaSymbol{)}
}\]
Reflexivity and transitivity are proved in a similar fashion.



\chapter{Square matrices over semirings\label{ch:Semi}}

% XXX Things that will have to be explained for this chapter to make sense:
% Fin; ∀-notation; open ... using notation; all the lemmas in Bigop.Properties; ℕ and Fin; pattern matching; the Matrix library (representation as Vec of Vecs; tabulate; lookup; syntax); universe levels and ⊔; REL A B ℓ; implicit arguments; records (constructors and fields); how algebraic structures publicly export / import the properties of their substructures; equational reasoning; propositional equality implies any other kind of equivalence via `reflexive`; binary operators and mixfix operators _⊕_ and _[_,_]

In this Chapter we present a proof that square matrices over a semiring themselves form a semiring. One explicit success criterion of this project was to make it possible to write this proof using our library.

\cref{Semi-Defs} introduces various definitions. In \cref{Semi-Plus} we show that square matrices and matrix addition constitute a commutative monoid with an annihilator. \cref{Semi-Times} proves that square matrices and matrix multiplication form a monoid. In \cref{Semi-Distr} we show that matrix multiplication distributes over matrix addition.


\section{\label{Semi-Defs}Definitions}

In this Section, we define matrix addition and multiplication, the zero matrix and the identity matrix.
All the code in this Chapter resides in a module that is parameterised over the underlying semiring and the size \AgdaBound{n} of the square matrices. The following declaration has the effect of fixing the variables \AgdaBound{n}, \AgdaBound{c}, \AgdaBound{ℓ} and \AgdaBound{semiring} in the module's body:

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
  open import Bigop.DecidableEquality using () renaming (≟F to ≟)
  import Bigop.Properties.Monoid
  import Bigop.Properties.CommutativeMonoid
  import Bigop.Properties.SemiringWithoutOne
  open import Bigop.Interval.Properties.Fin
  open import Matrix

  open import Algebra.Structures
  open import Data.Empty
  open import Data.Fin using (Fin) renaming (zero to zeroF; suc to sucF)
  open import Data.Fin.Properties using (bounded)
  import Data.List.Base as L using ([_])
  open import Data.Product using (proj₁; proj₂; _,_; uncurry)
  open import Function
  open import Level using (_⊔_)
  open import Relation.Nullary
  open import Relation.Unary
  open import Relation.Binary.Core using (_≡_; _≢_)
  open import Relation.Binary
  import Relation.Binary.Vec.Pointwise as PW
  import Relation.Binary.PropositionalEquality as P

  infix 4 _≋_
\end{code}
}
%TC:endignore
In the next listing, we bring the underlying semiring with its carrier type, special elements, operators and substructures into scope:\footnote{Here \emph{substructures} refers to the weaker structures that are automatically derived from the given algebraic structure by subtracting properties, operators or special elements. For example, any commutative monoid gives rise to a monoid if we take away the commutative law.} 
the commutative monoid, monoid and semigroup over \AgdaFunction{\_+\_}; the monoid and semigroup over \AgdaFunction{\_*\_}; and the \enquote{semiring without one} (a semiring-like structure without an identity for \AgdaFunction{\_*\_}).

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
Next, the equivalence relation \AgdaDatatype{\_≡\_} of the underlying setoid on \AgdaDatatype{Carrier} and its reflexive, symmetric and transitive laws (\AgdaField{refl}, \AgdaField{sym}, \AgdaField{trans}) are brought into scope. We make the sum syntax from the \AgdaModule{Bigop.Core.Fold} module available and open the modules containing lemmas about ordinals, equational reasoning functionality in the element setoid (\AgdaModule{EqReasoning}) and the module for equational reasoning with propositional equality (\AgdaModule{≡-Reasoning}). In order to avoid name clashes, the functions \AgdaFunction{begin\_}, \AgdaFunction{\_≡⟨\_⟩\_} and \AgdaFunction{\_∎} are renamed to \AgdaFunction{start\_}, \AgdaFunction{\_≣⟨\_⟩\_} and \AgdaFunction{\_□}, respectively.

%TC:ignore
\begin{code}
  open Setoid setoid using (_≈_; refl; sym; trans; reflexive; isEquivalence)
  open Fold +-monoid using (Σ-syntax)
  open import Bigop.Interval.Fin

  open import Relation.Binary.EqReasoning setoid
  open P.≡-Reasoning
    renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)
\end{code}
%TC:endignore
We define \AgdaDatatype{M} as a shorthand for the type of square matrices of size \AgdaBound{n} over the carrier of the underlying semiring. The pointwise lifting of the equivalence relation between elements is named \AgdaFunction{\_≋\_}. \AgdaDatatype{Matrix} and \AgdaDatatype{Pointwise} are defined in \cref{sc:Impl-Matrices}.

%TC:ignore
\begin{code}
  M : Set c
  M = Matrix Carrier n n

  _≋_ : Rel M ℓ
  _≋_ = Pointwise _≈_

  ≋-isEquivalence : IsEquivalence _≋_
  ≋-isEquivalence = PW-isEquivalence isEquivalence
\end{code}
%TC:endignore
Next we define matrix addition \AgdaFunction{\_⊕\_} and multiplication \AgdaFunction{\_⊗\_}. Addition works pointwise. 
%The function \AgdaFunction{tabulate} populates a matrix using a function that takes the row and column index to an element by applying that function to each position in the matrix.
The definition of \AgdaFunction{tabulate} is given in \cref{sc:Impl-Matrices}.

%TC:ignore
\begin{code}
  _⊕_ : M → M → M
  A ⊕ B = tabulate (λ r c → A [ r , c ] + B [ r , c ])
\end{code}
%TC:endignore
Using Σ-syntax, multiplication can be defined in a concise way:

%TC:ignore
\begin{code}
  mult : M → M → Fin n → Fin n → Carrier
  mult A B r c = Σ[ i ← 0 …< n ] A [ r , i ] * B [ i , c ]

  _⊗_ : M → M → M
  A ⊗ B = tabulate (mult A B)
\end{code}
%TC:endignore
Note how the definition of \AgdaFunction{mult} resembles the component-wise definition of matrix multiplication in standard mathematical notation: \[(A\,B)_{r,c} = \sum_{i ← 0 …<\ n} A_{r,i}\,B_{i,c}\]
The matrix \AgdaFunction{0M} is the identity for matrix addition and the annihilator for matrix multiplication. All of its elements are set to the zero element of the underlying semiring.

%TC:ignore
\begin{code}
  0M : M
  0M = tabulate (λ r c → 0#)
\end{code}
%TC:endignore
\AgdaFunction{1M} is the identity for matrix multiplication. Its definition relies on the function \AgdaFunction{diag}, which returns \AgdaFunction{1\#} (the multiplicative identity of the underlying semiring) if its arguments are equal and \AgdaFunction{0\#} (the additive identity and multiplicative annihilator of the underlying semiring) if they are different.

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

In this Section, we show that square matrices and matrix addition form a commutative monoid.


\minisec{Congruence}

% Usually in mathematical reasoning, we expect that replacing a subterm \(S\) by an equivalent subterm \(S′\) within a term \(T\) gives a term \(T[S′/S]\) that is equivalent to the original term, so \(S ≈ S′ ⇒ T ≈ T[S′/S]\). A special case of this is \(T = f(S)\) for some function \(f\). In a formal system like Agda, the \(f\)-property \(S ≈ S′ ⇒ f(S) ≈ f(S′)\) is called \emph{congruence} or \emph{preservation of equivalence} and must be proved for each function.

Here we prove that matrix addition preserves equivalence, that is, \AgdaBound{A}~\AgdaDatatype{≋}~\AgdaBound{A′}~\AgdaSymbol{→} \AgdaBound{B}~\AgdaDatatype{≋}~\AgdaBound{B′}~\AgdaSymbol{→} \AgdaBound{A}~\AgdaFunction{⊕}~\AgdaBound{B}~\AgdaDatatype{≋}~\AgdaBound{A′}~\AgdaFunction{⊕}~\AgdaBound{B′}.
\begin{align}
(A ⊕ B)_{r,c} &≈ A_{r,c} + B_{r,c} \\
              &≈ A′_{r,c} + B′_{r,c} \\
              &≈ (A′ ⊕ B′)_{r,c}
\end{align}
To show that two matrices are \AgdaDatatype{≋}-equivalent, we need to prove that their elements are \AgdaDatatype{≈}-equivalent. This dictates the structure of \AgdaFunction{⊕-cong} and all other proofs of matrix equivalence: an (equational reasoning style) proof of element-wise equivalence, abstracted over the row and column index.

In the inner proof, we first expand the definitions of \AgdaFunction{\_⊕\_} and \AgdaFunction{\_⊗\_}, then use the properties of the underlying operators \AgdaFunction{\_+\_} and \AgdaFunction{\_*\_} (in this case, congruence of \AgdaFunction{\_+\_}), and finally re-assemble the matrix operators.

%TC:ignore
\begin{code}
  ⊕-cong : ∀ {A A′ B B′} → A ≋ A′ → B ≋ B′ → A ⊕ B ≋ A′ ⊕ B′
  ⊕-cong {A} {A′} {B} {B′} eq₀ eq₁ = λ r c →
    begin
{- 4.1 -}  (A ⊕ B) [ r , c ]             ≡⟨ lookup∘tabulate r c ⟩
{- 4.2 -}  A [ r , c ]   + B [ r , c ]   ≈⟨ eq₀ r c ⟨ +-cong ⟩ eq₁ r c ⟩
{- 4.3 -}  A′ [ r , c ]  + B′ [ r , c ]  ≡⟨ P.sym (lookup∘tabulate r c) ⟩
           (A′ ⊕ B′) [ r , c ]
    ∎
    where
      open Semigroup +-semigroup using () renaming (∙-cong to +-cong)
\end{code}
%TC:endignore
Since the only law used in this proof is \AgdaFunction{+-cong}, the semigroup over \AgdaFunction{\_+\_} induced by the underlying semiring is sufficient to prove that matrix addition is congruent.


\minisec{Associativity}

The next proof shows that matrix addition is associative, that is, \AgdaSymbol{(}\AgdaBound{A} \AgdaFunction{⊕} \AgdaBound{B}\AgdaSymbol{)} \AgdaFunction{⊕} \AgdaBound{C} \AgdaDatatype{≋} \AgdaBound{A} \AgdaFunction{⊕} \AgdaSymbol{(}\AgdaBound{B} \AgdaFunction{⊕} \AgdaBound{C}\AgdaSymbol{)}. Since matrix addition is defined as elementwise addition, the proof of elementwise equivalence has the exact same structure as the congruence proof above: unfold the definition of \AgdaFunction{\_⊕\_}; use the appropriate properties (associativity in this case) of the elementwise addition \AgdaFunction{\_+\_}; fold back into matrix addition.

In standard mathematical notation, associativity of matrix addition can be proved as follows:
\begin{align}
((A ⊕ B) ⊕ C)_{r,c} &≈ (A_{r,c} + B_{r,c}) + C_{r,c} \\
&≈ A_{r,c} + (B_{r,c} + C_{r,c}) \\
&≈ (A ⊕ (B ⊕ C))_{r,c}
\end{align}
The auxiliary functions \AgdaFunction{⟨⊕⟩⊕-expand} and \AgdaFunction{⊕⟨⊕⟩-expand} simply unfold the nested matrix additions.

%TC:ignore
\begin{code}
  ⊕-assoc : ∀ A B C → (A ⊕ B) ⊕ C ≋ A ⊕ (B ⊕ C)
  ⊕-assoc A B C = λ r c → begin
{- 4.4 -}  ((A ⊕ B) ⊕ C) [ r , c ]                     ≡⟨ ⟨⊕⟩⊕-expand r c ⟩
{- 4.5 -}  (A [ r , c ] +  B [ r , c ]) + C [ r , c ]  ≈⟨ +-assoc _ _ _ ⟩
{- 4.6 -}  A [ r , c ] + (B [ r , c ]  + C [ r , c ])  ≡⟨ P.sym (⊕⟨⊕⟩-expand r c) ⟩
           (A ⊕ (B ⊕ C)) [ r , c ]                     ∎
           where
             open Semigroup +-semigroup using () renaming (assoc to +-assoc)
\end{code}
\AgdaHide{
\begin{code}
             ⟨⊕⟩⊕-expand : ∀ r c → ((A ⊕ B) ⊕ C) [ r , c ] ≡ (A [ r , c ] + B [ r , c ]) + C [ r , c ]
             ⟨⊕⟩⊕-expand r c =
               lookup∘tabulate r c ⟨ P.trans ⟩ P.cong₂ _+_ (lookup∘tabulate r c) P.refl

             ⊕⟨⊕⟩-expand : ∀ r c → (A ⊕ (B ⊕ C)) [ r , c ] ≡ A [ r , c ] + (B [ r , c ] + C [ r , c ])
             ⊕⟨⊕⟩-expand r c =
               lookup∘tabulate r c ⟨ P.trans ⟩ P.cong₂ _+_ P.refl (lookup∘tabulate r c)
\end{code}
}
%TC:endignore
Again, a semigroup over \AgdaFunction{\_+\_} provides sufficient structure to allow the proof to go through.


\minisec{Left identity}

Adding the zero matrix to any matrix \(A\) simply gives \(A\) as a result. In order to prove this, we first expand the definition of matrix addition. Then by definition, \AgdaFunction{0M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} (\(\mathbf{0}_{r,c}\) in mathematical notation) is equal to \AgdaFunction{0\#} for any \AgdaBound{r} and \AgdaBound{c}. The left identity law of the underlying monoid over \AgdaFunction{\_+\_} then justifies the equivalence:
\begin{align}
(\mathbf{0} ⊕ A)_{r,c} &≈ \mathbf{0}_{r,c} + A_{r,c} \\
&≈ 0 + A_{r,c} \\
&≈ A_{r,c}
\end{align}
Using equational reasoning, the corresponding Agda proof looks like this:

%TC:ignore
\begin{code}
  ⊕-identityˡ : ∀ A → 0M ⊕ A ≋ A
  ⊕-identityˡ A = λ r c →
    begin
{- 4.7 -}  (0M ⊕ A) [ r , c ]           ≡⟨ lookup∘tabulate r c ⟩
{- 4.8 -}  0M [ r , c ] +  A [ r , c ]  ≡⟨ P.cong₂ _+_ (lookup∘tabulate r c) P.refl ⟩
{- 4.9 -}            0# +  A [ r , c ]  ≈⟨ proj₁ +-identity _ ⟩
                           A [ r , c ]
    ∎
    where
      open Monoid +-monoid using () renaming (identity to +-identity)
\end{code}
%TC:endignore
Note that this proof makes use of \AgdaFunction{+-identity}, which \AgdaFunction{+-semigroup} does not provide. This is why we open the monoid over \AgdaFunction{\_+\_} in the identity proof above.

\minisec{Commutativity of matrix addition}

The commutativity proof follows the now-familiar pattern: first we use the definition of matrix addition, then apply the appropriate law from the underlying structure (in this case, the commutativity law of the commutative monoid over elementwise addition), and finally we rewrite the term again using the definition of addition.

Again, we present the proof in standard mathematical notation and then in Agda:
\begin{align}
(A ⊕ B)_{r,c} &≈ A_{r,c} + B_{r,c} \\
              &≈ B_{r,c} + A_{r,c} \\
              &≈ (B ⊕ A)_{r,c}
\end{align}

%TC:ignore
\begin{code}
  ⊕-comm : ∀ A B → A ⊕ B ≋ B ⊕ A
  ⊕-comm A B = λ r c →
    begin
{- 4.10 -}  (A ⊕ B) [ r , c ]           ≡⟨ lookup∘tabulate r c ⟩
{- 4.11 -}  A [ r , c ]  + B [ r , c ]  ≈⟨ +-comm _ _ ⟩
{- 4.12 -}  B [ r , c ]  + A [ r , c ]  ≡⟨ P.sym (lookup∘tabulate r c) ⟩
            (B ⊕ A) [ r , c ]
    ∎
    where
      open CommutativeMonoid +-commutativeMonoid using ()
        renaming (comm to +-comm)
\end{code}
%TC:endignore
Here \AgdaFunction{\_+\_} must be a commutative operator for the proof to go through.

\minisec{Matrix addition: a commutative monoid}

Putting all the lemmas in this Section together, we have shown that matrix addition forms a commutative monoid over square matrices with \AgdaFunction{0M} as its identity:

%TC:ignore
\begin{code}
  ⊕-isCommutativeMonoid : IsCommutativeMonoid _≋_ _⊕_ 0M
  ⊕-isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = ≋-isEquivalence
        ; assoc         = ⊕-assoc
        ; ∙-cong        = ⊕-cong
        }
      ; identityˡ       = ⊕-identityˡ
      ; comm            = ⊕-comm
      }
\end{code}
%TC:endignore

\section{\label{Semi-Times}Properties of matrix multiplication}

In this Section we prove that matrix multiplication is monoidal. Additionally, a proof is given that \AgdaFunction{0M} is a left zero for matrix multiplication.


\minisec{Congruence of matrix multiplication}

In this proof we need to use both \AgdaFunction{Σ.cong} and \AgdaFunction{*-cong} to replace equals by equals in a multiplication wrapped in a sum. The structure of the proof is unchanged from the last Section. See \cref{ssc:Monoid-lemmas} for a description of the lemmas contained in \AgdaModule{Bigop.Properties.Monoid}.
\begin{align}
(A ⊗ B)_{r,c} &≈ \sum_{i ← 0 …<\;n} A_{r,i}\;B_{i,c} \\
             &≈ \sum_{i ← 0 …<\;n} A′_{r,i}\;B′_{i,c} \\
             &≈ (A′ ⊗ B′)_{r,c}
\end{align}
%TC:ignore
\begin{code}
  ⊗-cong : ∀ {A A′ B B′} → A ≋ A′ → B ≋ B′ → A ⊗ B ≋ A′ ⊗ B′
  ⊗-cong {A} {A′} {B} {B′} eq₁ eq₂ = λ r c →
    begin
      (A ⊗ B) [ r , c ]
{- 4.13 -}       ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * B [ i , c ]
{- 4.14 -}       ≈⟨ Σ.cong (0 …< n) P.refl (λ i → *-cong (eq₁ r i) (eq₂ i c)) ⟩
      Σ[ i ← 0 …< n ] A′ [ r , i ] * B′ [ i , c ]
{- 4.15 -}       ≡⟨ P.sym (lookup∘tabulate r c) ⟩
      (A′ ⊗ B′) [ r , c ]
    ∎
    where
      open Semigroup *-semigroup using () renaming (∙-cong to *-cong)
      module Σ = Bigop.Properties.Monoid +-monoid using (cong)
\end{code}
%TC:endignore
We can read off the \AgdaKeyword{open} statements that this proof requires a semigroup over \AgdaFunction{\_*\_} and a monoid over \AgdaFunction{\_+\_}.

\minisec{Left zero for matrix multiplication}

In this proof that \AgdaFunction{0M} is the left zero for \AgdaFunction{\_⊗\_}, that is, \AgdaFunction{0M} \AgdaFunction{⊗} \AgdaBound{A} \AgdaDatatype{≋} \AgdaFunction{0M}, we use two lemmas from \AgdaModule{Bigop.Properties}.

% As described in XXX, \AgdaFunction{Σ.cong} states that if lists \AgdaBound{is} and \AgdaBound{js} are propositionally equal and functions \AgdaBound{f} and \AgdaBound{g} are extensionally equal with respect to \AgdaDatatype{\_≈\_}, then \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaBound{is} \AgdaFunction{]} \AgdaBound{f} \AgdaBound{i} \AgdaDatatype{≈} \AgdaFunction{Σ[} \AgdaBound{j} \AgdaFunction{←} \AgdaBound{js} \AgdaFunction{]} \AgdaBound{g} \AgdaBound{j}.

\begin{align}
(\mathbf{0} ⊗ A)_{r,c} &≈ \sum_{i ← 0 …<\;n} \mathbf{0}_{r,i}\;A_{i,c} \\
                       &≈ \sum_{i ← 0 …<\;n} 0\;A_{i,c} \\
                       &≈ 0 · \sum_{i ← 0 …<\;n} A_{i,c} \\
                       &≈ 0 \\
                       &≈ \mathbf{0}_{r,c}
\end{align}

%TC:ignore
\begin{code}
  M-zeroˡ : ∀ A → 0M ⊗ A ≋ 0M
  M-zeroˡ A = λ r c →
    begin
{- 4.16 -}  (0M ⊗ A) [ r , c ]                       ≡⟨ lookup∘tabulate r c ⟩
            Σ[ i ← 0 …< n ] 0M [ r , i ] * A [ i , c ]
              ≈⟨ Σ.cong  (0 …< n) P.refl
                         (λ i → reflexive (lookup∘tabulate r i) ⟨ *-cong ⟩ refl) ⟩
            Σ[ i ← 0 …< n ] 0# * A [ i , c ]
              ≈⟨ Σ.cong (0 …< n) P.refl (λ i → proj₁ zero _) ⟩
            Σ[ i ← 0 …< n ] 0#
              ≈⟨ Σ.identity (0 …< n) ⟩
{- 4.20 -}  0#                                       ≡⟨ P.sym (lookup∘tabulate r c) ⟩
            0M [ r , c ]
    ∎
    where
      open SemiringWithoutOne semiringWithoutOne using (*-cong; zero)
      module Σ = Bigop.Properties.Monoid +-monoid using (cong; identity)
\end{code}
%TC:endignore
Let us consider the second step of the proof in detail. The aim is to use \AgdaFunction{Σ.cong} to show
\[\text{\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…<} \AgdaBound{n} \AgdaFunction{]} \AgdaFunction{0M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}
\AgdaDatatype{≈}
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…<} \AgdaBound{n} \AgdaFunction{]} \AgdaFunction{0\#} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}}\]
On both sides of the equivalence, we take the sum over \AgdaSymbol{(}\AgdaNumber{0} \AgdaFunction{…<} \AgdaBound{n}\AgdaSymbol{)}. The proof that the lists are propositionally equal is therefore just \AgdaInductiveConstructor{P.refl}.

We now need to prove that \AgdaFunction{0M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≈} \AgdaFunction{0\#} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} for all \AgdaBound{i}. The outer form of this expression is a multiplication. Since our goal is to replace equal subterms by equal subterms, we need to use the appropriate congruence rule, \AgdaFunction{*-cong}. The right hand sides of the two multiplications are both \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}, so they are trivially equivalent by \AgdaFunction{refl}.

\AgdaFunction{0M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} is propositionally equal to \AgdaFunction{0\#} by (\AgdaFunction{lookup∘tabulate} \AgdaBound{r} \AgdaBound{i}). Equivalence in \AgdaDatatype{\_≈\_} follows from propositional equality by \AgdaFunction{reflexivity}, which proves that the left hand sides of the multiplications are ≈-equivalent too.

Putting this all together, we have built a term
\[ \text{\AgdaFunction{Σ.cong} \AgdaSymbol{(}\AgdaNumber{0} \AgdaFunction{…<} \AgdaBound{n}\AgdaSymbol{)} \AgdaInductiveConstructor{P.refl} \AgdaSymbol{(λ} \AgdaBound{i} \AgdaSymbol{→} \AgdaFunction{reflexive} \AgdaSymbol{(}\AgdaFunction{lookup∘tabulate} \AgdaBound{r} \AgdaBound{i}\AgdaSymbol{)} \AgdaFunction{⟨} \AgdaFunction{*-cong} \AgdaFunction{⟩} \AgdaFunction{refl}\AgdaSymbol{)} \AgdaFunction{⟩}} \]
proving the statement above.

In the remainder of the proof, we first apply the \AgdaFunction{zero} law of the underlying semiring and then \AgdaFunction{Σ.identity}, which shows that the sum of any number of zeros is zero. Right-distributivity is proved in a similar way. The proof is omitted here, but it is included in the Agda source files of the project.

%TC:ignore
\AgdaHide{
\begin{code}
  M-zeroʳ : ∀ A → A ⊗ 0M ≋ 0M
  M-zeroʳ A = λ r c →
    begin
      (A ⊗ 0M) [ r , c ]               ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * 0M [ i , c ]
        ≈⟨ Σ.cong  (0 …< n) P.refl
                   (λ i → *-cong refl (reflexive (lookup∘tabulate i c))) ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * 0#    ≈⟨ sym (Σ.distrʳ _ 0# (0 …< n)) ⟩
      (Σ[ i ← 0 …< n ] A [ r , i ]) * 0#  ≈⟨ proj₂ zero _ ⟩
      0#                               ≡⟨ P.sym (lookup∘tabulate r c) ⟩
      0M [ r , c ]
    ∎
    where
      open SemiringWithoutOne semiringWithoutOne using (*-cong; zero)
      module Σ = Bigop.Properties.SemiringWithoutOne semiringWithoutOne
\end{code}
}
%TC:endignore

\minisec{Associativity of matrix multiplication}

This proof is more involved than the associativity proof for matrix addition. The argument runs as follows:
\begin{align}
((A ⊗ B) ⊗ C)_{r,c}
&≈ \sum_{i\,←\,0 …<\,n} \left( \sum_{j\,←\,0 …<\,n} A_{r,j}\, B_{j,i} \right) C_{i,c}
    && \text{by the definition of ⊗} \\
&≈ \sum_{i\,←\,0 …<\,n} \sum_{j\,←\,0 …<\,n} (A_{r,j}\, B_{j,i}) C_{i,c}
    && \text{by right-distributivity} \\
&≈ \sum_{j\,←\,0 …<\,n} \sum_{i\,←\,0 …<\,n} (A_{r,j}\, B_{j,i}) C_{i,c}
    && \text{swapping the outer sums} \\
&≈ \sum_{j\,←\,0 …<\,n} \sum_{i\,←\,0 …<\,n} A_{r,j}\, (B_{j,i}\, C_{i,c})
    && \text{by associativity} \\
&≈ \sum_{j\,←\,0 …<\,n} A_{r,j} \sum_{i\,←\,0 …<\,n} B_{j,i}\, C_{i,c}
    && \text{by left-distributivity} \\
&≈ (A ⊗ (B ⊗ C))_{r,c}
    && \text{by the definition of ⊗}
\end{align}
In the Agda proof, we use the appropriate congruence rules to replace subterms by equivalent subterms. Steps (3.4) and (3.5) have been factored into a separate function \AgdaFunction{inner} to make the proof more readable. \AgdaFunction{⟨⊗⟩⊗-expand} and \AgdaFunction{⊗⟨⊗⟩-expand} unfold the nested matrix multiplications.

%TC:ignore
\begin{code}
  ⊗-assoc : ∀ A B C → (A ⊗ B) ⊗ C ≋ A ⊗ (B ⊗ C)
  ⊗-assoc A B C = λ r c →
    begin
      ((A ⊗ B) ⊗ C) [ r , c ]
{- 4.21 -}  ≈⟨ ⟨⊗⟩⊗-expand r c ⟩
      Σ[ i ← 0 …< n ] (Σ[ j ← 0 …< n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]
{- 4.22 -}  ≈⟨ Σ.cong (0 …< n) P.refl (λ i → Σ.distrʳ _ _ (0 …< n)) ⟩
      Σ[ i ← 0 …< n ] Σ[ j ← 0 …< n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
{- 4.23 -}  ≈⟨ Σ.swap _ (0 …< n) (0 …< n) ⟩
      Σ[ j ← 0 …< n ] Σ[ i ← 0 …< n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
            ≈⟨ Σ.cong (0 …< n) P.refl (inner r c) ⟩
      Σ[ j ← 0 …< n ] A [ r , j ] * (Σ[ i ← 0 …< n ] B [ j , i ] * C [ i , c ])
{- 4.26 -}  ≈⟨ sym $ ⊗⟨⊗⟩-expand r c ⟩
      (A ⊗ (B ⊗ C)) [ r , c ]
    ∎
    where
      open SemiringWithoutOne semiringWithoutOne using (*-assoc; *-cong)
      module Σ = Bigop.Properties.SemiringWithoutOne semiringWithoutOne
        using (cong; swap; distrˡ; distrʳ)
\end{code}
%TC:endignore
Within \AgdaFunction{⊗-assoc}, \AgdaFunction{inner} is used which proves steps (4.24) and (4.23):

%TC:ignore
\begin{code}
      inner : ∀ r c j →  Σ[ i ← 0 …< n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ] ≈
                         A [ r , j ] * (Σ[ i ← 0 …< n ] B [ j , i ] * C [ i , c ])
      inner r c j =
        begin
          Σ[ i ← 0 …< n ] (A [ r , j ] * B [ j , i ]) * C [ i , c ]
{- 4.24 -}  ≈⟨ Σ.cong (0 …< n) P.refl (λ i → *-assoc _ _ _) ⟩
          Σ[ i ← 0 …< n ] A [ r , j ] * (B [ j , i ] * C [ i , c ])
{- 4.25 -}  ≈⟨ sym (Σ.distrˡ _ _ (0 …< n)) ⟩
          A [ r , j ] * (Σ[ i ← 0 …< n ] B [ j , i ] * C [ i , c ])
        ∎
\end{code}
\AgdaHide{
\begin{code}
      ⟨⊗⟩⊗-expand : ∀ r c →  ((A ⊗ B) ⊗ C) [ r , c ] ≈
                             Σ[ i ← 0 …< n ] (Σ[ j ← 0 …< n ] A [ r , j ] * B [ j , i ]) * C [ i , c ]
      ⟨⊗⟩⊗-expand r c =
        reflexive (lookup∘tabulate r c) ⟨ trans ⟩
        Σ.cong (0 …< n) P.refl (λ i → *-cong (reflexive (lookup∘tabulate r i)) refl)

      ⊗⟨⊗⟩-expand : ∀ r c →  (A ⊗ (B ⊗ C)) [ r , c ] ≈
                             Σ[ j ← 0 …< n ] A [ r , j ] * (Σ[ i ← 0 …< n ] B [ j , i ] * C [ i , c ])
      ⊗⟨⊗⟩-expand r c =
        reflexive (lookup∘tabulate r c) ⟨ trans ⟩
        Σ.cong (0 …< n) P.refl (λ j → *-cong refl (reflexive (lookup∘tabulate j c)))
\end{code}
}
%TC:endignore
% $


\minisec{Left identity for matrix multiplication}

This is the longest of the semiring proofs. We show that \AgdaFunction{1M} \AgdaFunction{⊗} \AgdaBound{A} \AgdaDatatype{≋} \AgdaBound{A} for all \AgdaBound{A}. The key idea here is that for any term involving \AgdaFunction{1M}, we can perform a case split on whether the row \AgdaBound{r} and column \AgdaBound{c} are equal. If they are, then \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{1\#} by \AgdaFunction{1M-diag}. If not, then by \AgdaFunction{1M-∁-diag} we have \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{0\#}:

%TC:ignore
\begin{code}
  1M-diag : ∀ {r c} → r ≡ c → 1M [ r , c ] ≡ 1#
  1M-diag {r} {.r} P.refl = start
    1M [ r , r ]  ≣⟨ lookup∘tabulate r r ⟩
    diag r r      ≣⟨ diag-lemma r ⟩
    1#            □
      where  diag-lemma  : ∀ {n} (r : Fin n) → diag r r ≡ 1#
             diag-lemma  zeroF     =  P.refl
             diag-lemma  (sucF r)  =  diag-lemma r

  1M-∁-diag : ∀ {r c} → ∁ (_≡_ r) c → 1M [ r , c ] ≡ 0#
  1M-∁-diag {r} {c} eq with ≟ r c
  1M-∁-diag {r} {c} ¬eq | yes eq  = ⊥-elim (¬eq eq)
  1M-∁-diag {r} {c} ¬eq | no  _   = start
    1M [ r , c ]  ≣⟨ lookup∘tabulate r c ⟩
    diag r c      ≣⟨ diag-lemma r c ¬eq ⟩
    0#            □
      where
        suc-¬-lemma : ∀ {n} {r c : Fin n} → ¬ sucF r ≡ sucF c → ¬ r ≡ c
        suc-¬-lemma {r} ¬eq P.refl = ¬eq P.refl

        diag-lemma : ∀ {n} (r c : Fin n) → ¬ r ≡ c → diag r c ≡ 0#
        diag-lemma zeroF     zeroF     ¬eq  =  ⊥-elim (¬eq P.refl)
        diag-lemma zeroF     (sucF _)  _    =  P.refl
        diag-lemma (sucF r)  zeroF     ¬eq  =  P.refl
        diag-lemma (sucF r)  (sucF c)  ¬eq  =  diag-lemma r c (suc-¬-lemma ¬eq)
\end{code}
%TC:endignore
The justification for the identity law in mathematical notation is as follows:
\begin{align}
(\mathbf{1} ⊗ A)_{r,c} &≈ \sum_{i ← 0 …<\;n} \mathbf{1}_{r,i}\;A_{i,c} \\
                       &≈ \left( \sum_{\substack{i ← 0 …<\;n \\ r ≡ i}} \mathbf{1}_{r,i}\;A_{i,c} \right) + \left( \sum_{\substack{i ← 0 …<\;n \\ r ≢ i}} \mathbf{1}_{r,i}\;A_{i,c} \right) \\
                       &≈ \left( \sum_{\substack{i ← 0 …<\;n \\ r ≡ i}} 1 · A_{i,c} \right) + \left( \sum_{\substack{i ← 0 …<\;n \\ r ≢ i}} 0 · A_{i,c} \right) \\
                       &≈ \left( \sum_{\substack{i ← 0 …<\;n \\ r ≡ i}} A_{i,c} \right) + 0 \\
                       &≈ \sum_{\substack{i ← 0 …<\;n \\ r ≡ i}} A_{i,c} \\
                    %  &≈ A_{r,c} + 0 \\
                       &≈ A_{r,c}
\end{align}
After unfolding the definition of \AgdaFunction{⊗}, we split the list (\AgdaNumber{0} \AgdaFunction{…<} \AgdaBound{n}) that is being summed over by the decidable predicate (\AgdaFunction{≟} \AgdaBound{r}) using \AgdaFunction{Σ.split-P}. This lets us consider the cases \AgdaBound{r} \AgdaFunction{≡} \AgdaBound{i} and \AgdaBound{r} \AgdaFunction{≢} \AgdaBound{i} separately.
The function \AgdaFunction{≡-step} deals with the first case. From \AgdaBound{r} \AgdaFunction{≡} \AgdaBound{i} follows \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{1\#}. Using distributivity and the identity law for \AgdaFunction{\_*\_}, we can deduce that
\[ \text{
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…<} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{≟} \AgdaBound{r} \AgdaFunction{]} \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaFunction{≈}
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…<} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{≟} \AgdaBound{r} \AgdaFunction{]} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]}
}\]
Otherwise, \AgdaFunction{≢-step} assumes that \AgdaBound{r} \AgdaFunction{≢} \AgdaBound{i}. It follows that \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaDatatype{≡} \AgdaFunction{0\#}. By distributivity and the \AgdaFunction{zero} law of the underlying semiring we then have

\[ \text{
\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…<} \AgdaBound{n} \AgdaFunction{∥} \AgdaFunction{∁′} (\AgdaFunction{≟} \AgdaBound{r}) \AgdaFunction{]} \AgdaFunction{1M} \AgdaFunction{[} \AgdaBound{r} \AgdaFunction{,} \AgdaBound{i} \AgdaFunction{]} \AgdaFunction{*} \AgdaBound{A} \AgdaFunction{[} \AgdaBound{i} \AgdaFunction{,} \AgdaBound{c} \AgdaFunction{]} \AgdaFunction{≈}
\AgdaFunction{0\#}
}\]
%TC:ignore
\begin{code}
  ⊗-identityˡ : ∀ A → 1M ⊗ A ≋ A
  ⊗-identityˡ A = λ r c →
    begin
      (1M ⊗ A) [ r , c ]
{- 4.27 -}  ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] 1M [ r , i ] * A [ i , c ]
{- 4.28 -}  ≈⟨ Σ.split-P _ (0 …< n) (≟ r) ⟩
      Σ[ i ← 0 …< n ∥ ≟ r ]       1M [ r , i ] * A [ i , c ] +
      Σ[ i ← 0 …< n ∥ ∁′ (≟ r) ]  1M [ r , i ] * A [ i , c ]
{- 4.29 -}  ≈⟨ ≡-step r c ⟨ +-cong ⟩ ≢-step r c ⟩
      Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ] + 0#
{- 4.30 -}  ≈⟨ proj₂ +-identity _ ⟩
      Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ]
{- 4.31 -}  ≡⟨ P.cong  (Σ-syntax (λ i → A [ i , c ]))
                       (filter r c) ⟩
      A [ r , c ] + 0#
{- 4.32 -}  ≈⟨ proj₂ +-identity _  ⟩
      A [ r , c ]
    ∎
    where
      open Semiring semiring using (+-cong; +-identity; *-cong; *-identity; zero)
      module Σ = Bigop.Properties.SemiringWithoutOne semiringWithoutOne
        using (cong-P; split-P; distrˡ)

      ≡-step : ∀ r c →  Σ[ i ← 0 …< n ∥ ≟ r ] 1M [ r , i ] * A [ i , c ] ≈
                        Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ]
      ≡-step r c =
        begin
          Σ[ i ← 0 …< n ∥ ≟ r ] 1M [ r , i ] * A [ i , c ]
            ≈⟨ Σ.cong-P  (0 …< n) (≟ r)
                         (λ i r≡i → reflexive (1M-diag r≡i) ⟨ *-cong ⟩ refl) ⟩
          Σ[ i ← 0 …< n ∥ ≟ r ] 1# * A [ i , c ]
            ≈⟨ sym $ Σ.distrˡ _ 1# (0 …< n ∥ ≟ r) ⟩
          1# * (Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ])
            ≈⟨ proj₁ *-identity _ ⟩
          Σ[ i ← 0 …< n ∥ ≟ r ] A [ i , c ]
        ∎

      ≢-step : ∀ r c → Σ[ i ← 0 …< n ∥ ∁′ (≟ r) ] 1M [ r , i ] * A [ i , c ] ≈ 0#
      ≢-step r c =
        begin
          Σ[ i ← 0 …< n ∥ ∁′ (≟ r) ] 1M [ r , i ] * A [ i , c ]
            ≈⟨ Σ.cong-P  (0 …< n) (∁′ (≟ r))
                         (λ i r≢i → reflexive (1M-∁-diag r≢i) ⟨ *-cong ⟩ refl) ⟩
          Σ[ i ← 0 …< n ∥ ∁′ (≟ r) ] 0# * A [ i , c ]
            ≈⟨ sym $ Σ.distrˡ _ 0# (0 …< n ∥ ∁′ (≟ r)) ⟩
          0# * (Σ[ i ← 0 …< n ∥ (∁′ (≟ r)) ] A [ i , c ])
            ≈⟨ proj₁ zero _ ⟩
          0#
        ∎

      filter : ∀ r c → 0 …< n ∥ ≟ r ≡ L.[ r ]
      filter r c = ordinals-filter z≤n (bounded r)
\end{code}
%TC:endignore
\AgdaFunction{filter} is just an application of \AgdaFunction{ordinals-filterF}, which states that the list ordinals from \(m\) to \(m + n - 1\) includes every natural number between \(m\) and \(m + n - 1\) exactly once.

The proof of right-identity works in a similar way, and is omitted here. It is included in the Agda source of the project.

%TC:ignore
\AgdaHide{
\begin{code}
  ⊗-identityʳ : ∀ A → A ⊗ 1M ≋ A
  ⊗-identityʳ A = ident
    where
      open Semiring semiring using (+-cong; +-identity; *-cong; *-identity; zero)
      module Σ = Bigop.Properties.SemiringWithoutOne semiringWithoutOne

      ∁-sym : ∀ {a} {A : Set a} {A B : A} → ∁ (_≡_ A) B → ∁ (λ C → B ≡ C) A
      ∁-sym eq P.refl = eq P.refl

      ident : ∀ r c → (A ⊗ 1M) [ r , c ] ≈ A [ r , c ]
      ident r c = begin
        (A ⊗ 1M) [ r , c ]
          ≡⟨ lookup∘tabulate r c ⟩
        Σ[ i ← 0 …< n ] A [ r , i ] * 1M [ i , c ]
          ≈⟨ Σ.split-P _ (0 …< n) (≟ c) ⟩
        Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ] * 1M [ i , c ] +
        Σ[ i ← 0 …< n ∥ ∁′ (≟ c) ] A [ r , i ] * 1M [ i , c ]
          ≈⟨ +-cong
               (Σ.cong-P (0 …< n) (≟ c)
                         (λ i c≡i → *-cong refl
                                           (reflexive (1M-diag (P.sym c≡i)))))
               (Σ.cong-P (0 …< n) (∁′ (≟ c))
                         (λ i c≢i → *-cong refl
                                           (reflexive (1M-∁-diag (∁-sym c≢i))))) ⟩
        Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ] * 1# +
        Σ[ i ← 0 …< n ∥ ∁′ (≟ c) ] A [ r , i ] * 0#
          ≈⟨ sym $ +-cong (Σ.distrʳ _ 1# (0 …< n ∥ (≟ c)))
                          (Σ.distrʳ _ 0# (0 …< n ∥ ∁′ (≟ c))) ⟩
        (Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ]) * 1# +
        (Σ[ i ← 0 …< n ∥ (∁′ (≟ c)) ] A [ r , i ]) * 0#
          ≈⟨ +-cong (proj₂ *-identity _) (proj₂ zero _) ⟩
        (Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ]) + 0#
          ≈⟨ proj₂ +-identity _ ⟩
        Σ[ i ← 0 …< n ∥ (≟ c) ] A [ r , i ]
          ≡⟨ P.cong (Σ-syntax (λ i → A [ r , i ]))
                    (ordinals-filter z≤n (bounded c)) ⟩
        Σ[ i ← L.[ c ] ] A [ r , i ]
          ≈⟨ proj₂ +-identity _  ⟩
        A [ r , c ] ∎
\end{code}
}
%TC:endignore
% $

%TC:ignore
\begin{code}
  ⊗-isMonoid : IsMonoid _≋_ _⊗_ 1M
  ⊗-isMonoid = record
    { isSemigroup = record
      { isEquivalence = ≋-isEquivalence
      ; assoc         = ⊗-assoc
      ; ∙-cong        = ⊗-cong
      }
    ; identity        = ⊗-identityˡ , ⊗-identityʳ
    }
\end{code}
%TC:endignore

\section{\label{Semi-Distr}Distributivity laws}

Here we prove that \AgdaFunction{\_⊗\_} right-distributes over \AgdaFunction{\_⊕\_}. The proof of left-distributivity works in a similar way, and is omitted in this report.

This proof shows that \AgdaBound{A} \AgdaFunction{⊗} \AgdaSymbol{(}\AgdaBound{B} \AgdaFunction{⊕} \AgdaBound{C}\AgdaSymbol{)} \AgdaDatatype{≋} \AgdaSymbol{(}\AgdaBound{A} \AgdaFunction{⊗} \AgdaBound{B}\AgdaSymbol{)} \AgdaFunction{⊕} \AgdaSymbol{(}\AgdaBound{A} \AgdaFunction{⊗} \AgdaBound{C}\AgdaSymbol{)}. Most of the proof is concerned with unfolding the definition of \AgdaFunction{\_⊕\_} and \AgdaFunction{\_⊗\_}. The crucial step in the proof is the application of the left-distributivity law of the underlying semiring in \AgdaFunction{inner} followed by the use of \AgdaFunction{Σ.merge} in \AgdaFunction{distr}, splitting the sum into two.

\begin{align}
(A ⊗ (B ⊕ C))_{r,c} &≈ \sum_{i ← 0 …<\;n} A_{r,i} (B_{i,c} + C_{i,c}) \\
                    &≈ \sum_{i ← 0 …<\;n} (A_{r,i}\;B_{i,c}) + (A_{r,i}\;C_{i,c}) \\
                    &≈ \left( \sum_{i ← 0 …<\;n} A_{r,i}\;B_{i,c} \right) + \left( \sum_{i ← 0 …<\;n} A_{r,i}\;C_{i,c} \right) \\
                    &≈ (A ⊗ B)_{r,c} + (A ⊗ C)_{r,c} \\
                    &≈ ((A ⊗ B) ⊕ (A ⊗ C))_{r,c}
\end{align}
%TC:ignore
\begin{code}
  ⊗-distrOverˡ-⊕ : ∀ A B C → A ⊗ (B ⊕ C) ≋ (A ⊗ B) ⊕ (A ⊗ C)
  ⊗-distrOverˡ-⊕ A B C = λ r c →
    begin
      (A ⊗ (B ⊕ C)) [ r , c ]
{- 4.33 -}  ≡⟨ lookup∘tabulate r c ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * (B ⊕ C) [ i , c ]
{- 4.34 -}  ≈⟨ Σ.cong (0 …< n) P.refl (inner r c)⟩
      Σ[ i ← 0 …< n ] (  A [ r , i ] * B [ i , c ] +
                      A [ r , i ] * C [ i , c ])
{- 4.35 -}  ≈⟨ sym $ Σ.merge _ _ (0 …< n) ⟩
      Σ[ i ← 0 …< n ] A [ r , i ] * B [ i , c ] +
      Σ[ i ← 0 …< n ] A [ r , i ] * C [ i , c ]
{- 4.36 -}  ≡⟨ P.sym $ lookup∘tabulate r c ⟨ P.cong₂ _+_ ⟩ lookup∘tabulate r c ⟩
      (A ⊗ B) [ r , c ] + (A ⊗ C) [ r , c ]
{- 4.37 -}  ≡⟨ P.sym $ lookup∘tabulate r c ⟩
      ((A ⊗ B) ⊕ (A ⊗ C)) [ r , c ]
    ∎
    where
      open Semiring semiring using (*-cong; distrib)
      module Σ = Bigop.Properties.CommutativeMonoid +-commutativeMonoid
        using (cong; merge)

      inner : ∀ r c i → A [ r , i ] * (B ⊕ C) [ i , c ] ≈
                        A [ r , i ] * B [ i , c ] + A [ r , i ] * C [ i , c ]
      inner r c i =
        begin
          A [ r , i ] * (B ⊕ C) [ i , c ]
            ≈⟨ refl ⟨ *-cong ⟩ reflexive (lookup∘tabulate i c) ⟩
          A [ r , i ] * (B [ i , c ] + C [ i , c ])
            ≈⟨ proj₁ distrib _ _ _ ⟩
          A [ r , i ] * B [ i , c ] + A [ r , i ] * C [ i , c ]
        ∎
\end{code}
%TC:endignore
% $

%TC:ignore
\AgdaHide{
\begin{code}
  ⊗-distrOverʳ-⊕ : ∀ A B C → (B ⊕ C) ⊗ A ≋ (B ⊗ A) ⊕ (C ⊗ A)
  ⊗-distrOverʳ-⊕ A B C = distr
    where
      open Semiring semiring using (*-cong; distrib)
      module Σ = Bigop.Properties.SemiringWithoutOne semiringWithoutOne

      distr : ∀ r c → ((B ⊕ C) ⊗ A) [ r , c ] ≈ ((B ⊗ A) ⊕ (C ⊗ A)) [ r , c ]
      distr r c = begin
        ((B ⊕ C) ⊗ A) [ r , c ]
          ≡⟨ lookup∘tabulate r c ⟩
        Σ[ i ← 0 …< n ] (B ⊕ C) [ r , i ] * A [ i , c ]
          ≈⟨ Σ.cong (0 …< n) P.refl (λ i → begin

            (B ⊕ C) [ r , i ] * A [ i , c ]
              ≈⟨ *-cong (reflexive (lookup∘tabulate r i)) refl ⟩
            (B [ r , i ] + C [ r , i ]) * A [ i , c ]
              ≈⟨ proj₂ distrib _ _ _ ⟩
            (B [ r , i ] * A [ i , c ]) + (C [ r , i ] * A [ i , c ]) ∎)⟩

        Σ[ i ← 0 …< n ] ((B [ r , i ] * A [ i , c ]) + (C [ r , i ] * A [ i , c ]))
          ≈⟨ sym (Σ.merge _ _ (0 …< n)) ⟩
        Σ[ i ← 0 …< n ] B [ r , i ] * A [ i , c ] +
        Σ[ i ← 0 …< n ] C [ r , i ] * A [ i , c ]
          ≡⟨ P.sym $ P.cong₂ _+_ (lookup∘tabulate r c) (lookup∘tabulate r c) ⟩
        (B ⊗ A) [ r , c ] + (C ⊗ A) [ r , c ]
          ≡⟨ P.sym (lookup∘tabulate r c) ⟩
        ((B ⊗ A) ⊕ (C ⊗ A)) [ r , c ] ∎
\end{code}
}
%TC:endignore
% $

\section{Summary}

Taking all the lemmas in this Chapter together, we have shown that square matrices over a semiring again form a semiring:

%TC:ignore
\begin{code}
  M-isSemiring : IsSemiring _≋_ _⊕_ _⊗_ 0M 1M
  M-isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid  = ⊕-isCommutativeMonoid
      ; *-isMonoid             = ⊗-isMonoid
      ; distrib                = ⊗-distrOverˡ-⊕ , ⊗-distrOverʳ-⊕
      }
    ; zero                     = M-zeroˡ , M-zeroʳ
    }

  M-Semiring : Semiring c ℓ
  M-Semiring = record
    { Carrier     = M
    ; _≈_         = _≋_
    ; _+_         = _⊕_
    ; _*_         = _⊗_
    ; 0#          = 0M
    ; 1#          = 1M
    ; isSemiring  = M-isSemiring
    }
\end{code}
%TC:endignore

\chapter{Conclusions\label{ch:Concl}}

The success criterion of this project as described in the project proposal was to build a set of reusable libraries that make it possible to write a readable proof of the theorem \enquote{square matrices over a semiring form a semiring} in Agda.%
\footnote{The wording in the proposal was \enquote{any square matrix over a semiring is a semiring}, which is incorrect: one square matrix by itself does not constitute a semiring. The intended meaning was \enquote{square matrices over a semiring form a semiring}.} %
This criterion has been met:
\begin{itemize}
\item We have implemented a library for expressing and reasoning about big operators in an algebra-centric way.
\item Additionally, modules for expressing and reasoning about matrices, intervals of natural numbers and filters have been implemented.
\item The four components of the library (big operators, matrices, intervals and filters) are independent but can easily be combined. All four are written in idiomatic Agda, and have been designed to interoperate with the Agda standard library.
\item Propositions involving big operators can be written in a notation that resembles pen-and-paper mathematics using special syntax defined in each component.
\item We have proved that square matrices over a semiring form a semiring (see \cref{ch:Semi}). The proof demonstrates the use of all four components of our library.
\end{itemize}

In our project proposal we claimed that any implementation of big operators would depend on \enquote{a notion of enumerable finite sets}. Experiments with prototype implementations using finite sets showed that this additional layer of abstraction only complicated the implementation with no tangible benefits. In \cref{ssc:as-lists} we argue that lists are the most idiomatic way to represent the collection of indices of a big operator.


\section{Related work}

In this section, we relate our project to previous implementations of big operators in the proof assistants Isabelle and Coq.

\subsection{Isabelle: List.thy and Groups\_Big.thy}

Isabelle's higher-order logic (HOL) library contains two definitions related to big operators.

\begin{itemize}
\item The module \texttt{Groups\_Big} defines a Sigma-notation for big operators. Here, sets represent the collection of indices, and the underlying structure is assumed to be a commutative monoid (see \cref{sc:Design} for how the representation of the index domain and the algebraic structure are related).
\item The \texttt{List} theory defines a function \texttt{listsum}, which exactly corresponds to the function \AgdaFunction{crush} defined in \cref{ssc:Implementing}: given a monoid, it performs a right-fold over the list, combining elements using the monoid's operator. If the list is empty, the identity element of the monoid is returned. No syntax definitions for \texttt{listsum} is provided.
\end{itemize}

In contrast to Agda, there has been a large effort in Isabelle to formalise set theory, so building on top of sets as fundamental building block is a natural path to take. Since lists are have more structure than sets (see \cref{ssc:as-lists}), we would argue that defining big operators over lists rather than sets is the more flexible, unifying approach.

\subsection{Coq: bigop.v}

The approach taken in Coq's \texttt{bigop} module,%
\footnote{A clickable version of the source code for the \texttt{bigop} module can be accessed via \url{http://ssr.msr-inria.inria.fr/doc/mathcomp-1.5/MathComp.bigop.html}.} %
which is part of the Mathematical Components library (and formerly of SSReflect), provided much inspiration for this project.%
\footnote{The source code and documentation of both SSReflect and the Mathematical Components library for Coq can be found here: \url{http://ssr.msr-inria.inria.fr/}.} %
Internally, the library works in a very similar way to ours: in a monoid, \AgdaFunction{fold} (defined in \cref{ssc:Implementing}) is equivalent to \texttt{reducebig}, the big operator evaluation function in \texttt{bigop} (see \cref{sc:Reducebig} for a formal proof). One big difference is that there is no restriction on the underlying structure---\texttt{reducebig} does not require a monoid.

Lemmas, on the other hand, are structured in a similar way to our project: sections of the module assume certain properties of the underlying structure, and prove lemmas about big operators based on those assumptions.

The \texttt{bigop} module is more comprehensive than our library. It provides a lot of flexibility in terms of notation, and allows users to define big operators over sets, finite types and enumerable predicates (all of which are converted to lists internally).

\section{Future work\label{sc:Future}}

We aim to make our library publically available in the near future. In order to make it more accessible to both users and contributors and improve maintainability, we will try to simplify the structure of the source code.

In order to make the library more useful in a wider range of scenarios, it will be extended to include lemmas about more algebraic structures. As a simple example, in an \emph{abelian group} (a commutative monoid with inverses for each carrier element) the following holds:
\[ \left( \prod_i f(i) \right) · \left( \prod_i \frac{1}{f(i)} \right) = 0 \]
It would be interesting to see what other properties can be lifted from different underlying algebraic structures.

A different but related idea would be to attempt to write a solver for big operators over some algebraic structure. Agda's standard library already contains solvers for monoids (\AgdaModule{Algebra.Monoid-solver}) and rings (\AgdaModule{Algebra.RingSolver}).%
\footnote{Eric Mertens wrote a number of solvers for different algebraic structures in Agda, available here: \url{https://github.com/glguy/my-agda-lib/tree/master/Algebra}.} %
The challenge here would be to find a normal form for complex big operator expressions to reduce to.

%TC:ignore
\appendix

\printbibliography

\chapter{Source code structure}

\begin{figure}[h!]
\begin{verbatim}
├── Bigop.agda                           19
├── Bigop
│   ├── Core.agda                        35
│   ├── Core
│   │   └── Properties.agda              14
│   ├── Properties
│   │   ├── BooleanAlgebra.agda          45
│   │   ├── CommutativeMonoid.agda       92
│   │   ├── Monoid.agda                  87
│   │   └── SemiringWithoutOne.agda      30
│   ├── DecidableEquality.agda           29
│   ├── Filter.agda                      14
│   ├── Filter
│   │   ├── PredicateReasoning.agda      23
│   │   ├── Predicates.agda              40
│   │   └── Properties.agda              89
│   └── Interval
│       ├── Fin.agda                     23
│       ├── Nat.agda                     12
│       └── Properties
│           ├── Fin.agda                 63
│           └── Nat.agda                 69
├── Matrix.agda                          59
├── GaussProofs.agda                     89
├── BinomialTheorem.agda                114
└── SemiringProof.agda                  371
\end{verbatim}
\caption{Agda source files and lines of code. The module structure uses conventions of the Agda standard library.}
\label{fig:structure}
\end{figure}





\chapter{Predicate example\label{ch:Collatz}}

\AgdaHide{
\begin{code}
module Collatz-example where
  open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

  open import Data.Fin
  open import Data.Nat.Base hiding (_⊔_)
  open import Data.Nat.DivMod
  open import Data.Product hiding (∃; curry; uncurry)
  open import Relation.Binary.PropositionalEquality
\end{code}
}


As an example of a more involved predicate that uses propositional equality in its definition, \AgdaDatatype{Collatz} \AgdaBound{n} provides evidence that if we keep iterating the function \AgdaFunction{f} (defined below), starting with \AgdaFunction{f} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{n}\AgdaSymbol{)}, eventually the result will be the number one.
\[ f(n) =
	\begin{cases}
		n/2    & \text{if } n \equiv 0 \text{ (mod \(2\))} \\
		3n + 1 & \text{if } n \equiv 1 \text{ (mod \(2\))}
	\end{cases}
\]
We can provide evidence for this property by giving a natural number \AgdaBound{i} together with a proof that \AgdaFunction{iter} \AgdaFunction{f} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{n}\AgdaSymbol{)} \AgdaBound{i} \AgdaDatatype{≡} \AgdaNumber{1}. Bundling a value and evidence for a property of that value together is the constructive version of the existential quantifier. The record type \AgdaDatatype{Σ} defined in \cref{ssc:Records} is exactly what we require: \AgdaDatatype{Σ} \AgdaDatatype{ℕ} (\AgdaSymbol{λ} \AgdaBound{i} \AgdaSymbol{→} \AgdaFunction{iter} (\AgdaInductiveConstructor{suc} \AgdaBound{n}) \AgdaBound{i} \AgdaDatatype{≡} \AgdaNumber{1}). Since the type of the value (\AgdaDatatype{ℕ}) is unambiguous from the context, we can define yet another shortcut for \AgdaDatatype{Σ} where this type is inferred by Agda:

\begin{code}
  ∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
  ∃ = Σ _
\end{code}
This lets us define a type \AgdaDatatype{∃} \AgdaSymbol{λ} \AgdaBound{x} \AgdaSymbol{→} \AgdaSymbol{…}, which reads naturally as \enquote{there exists an \AgdaBound{x} such that …}. We now have all the building blocks to write the predicate \AgdaDatatype{Collatz}:

\begin{code}
  Collatz : ℕ → Set
  Collatz n = ∃ λ i → iter f (suc n) i ≡ 1
    where
      f : ℕ → ℕ
      f n with n mod 2
      f n | zero      = n div 2
      f n | suc zero  = suc (3 * n)
      f n | suc (suc ())

      iter : ∀ {A} → (A → A) → A → ℕ → A
      iter f x zero     = x
      iter f x (suc i)  = iter f (f x) i
\end{code}
The function \AgdaFunction{iter} \AgdaBound{f} \AgdaBound{x} \AgdaBound{i} simply applies \AgdaBound{f} to \AgdaBound{x}, \AgdaBound{i} times:

\[
\text{\AgdaFunction{iter} \AgdaBound{f} \AgdaBound{x} \AgdaBound{i}}
= (\underbrace{\AgdaBound{f} ∘ \AgdaBound{f} ∘ ⋯ ∘ \AgdaBound{f}}_{\text{\AgdaBound{i} times}})\;\AgdaBound{x}
\]

In the definition of \AgdaFunction{f}, there is one piece of syntax that we have not come across so far: \AgdaKeyword{with} lets us pattern match against the result of evaluating an arbitrary expression and updates the local context with any new type information gleaned from that pattern match. The return value of \AgdaFunction{f} depends on whether \AgdaBound{n} is divisible by two. The expression \AgdaBound{n} \AgdaFunction{mod} \AgdaNumber{2} gives the remainder of dividing \AgdaBound{n} by two, the result of which is either \AgdaInductiveConstructor{zero} or \AgdaInductiveConstructor{suc} \AgdaInductiveConstructor{zero}. Here the absurd pattern is required---if we leave it out, the totality checker complains. It indicates that there is no \AgdaBound{m} such that \AgdaBound{n} \AgdaFunction{mod} \AgdaNumber{2} equals \AgdaInductiveConstructor{suc} (\AgdaInductiveConstructor{suc} \AgdaBound{m}).

Let's look at a few examples of \AgdaDatatype{Collatz} \AgdaBound{n}. With \(\AgdaBound{n} = \AgdaNumber{0}\), we have to give an \AgdaBound{i} such that the result of applying \AgdaFunction{f} to \AgdaInductiveConstructor{suc} \AgdaNumber{0} evaluates to \AgdaNumber{1}. But we already have \(\AgdaInductiveConstructor{suc}\;\AgdaNumber{0} = \AgdaNumber{1}\), so we do not need to apply \AgdaFunction{f} at all and \(\AgdaBound{i} = \AgdaNumber{0}\).

Note that in all these examples, the second element of the pair, which represents the proof \AgdaFunction{iter} (\AgdaInductiveConstructor{suc} \AgdaBound{n}) \AgdaBound{i} \AgdaDatatype{≡} \AgdaNumber{1}, is just \AgdaInductiveConstructor{refl}: given \AgdaBound{i}, the type checker can evaluate the iteration and figure out that the equality holds.

\begin{code}
  Collatz‿0+1 : Collatz 0
  Collatz‿0+1 = 0 , refl
\end{code}
With \(\AgdaBound{n} = \AgdaInductiveConstructor{suc}\;\AgdaNumber{1}\), the remainder after division by two is zero, so we do the division and get to \AgdaNumber{1} in one iteration: \(\AgdaBound{i} = \AgdaNumber{1}\).

\begin{code}
  Collatz‿1+1 : Collatz 1
  Collatz‿1+1 = 1 , refl
\end{code}
For \(\AgdaBound{n} = \AgdaInductiveConstructor{suc}\;\AgdaNumber{3}\), we divide by two twice to get to \AgdaNumber{1}, giving \(\AgdaBound{i} = \AgdaNumber{2}\).

\begin{code}
  Collatz‿3+1 : Collatz 3
  Collatz‿3+1 = 2 , refl
\end{code}
As the following diagram shows, we need to apply \AgdaFunction{f} seven times to get from \AgdaInductiveConstructor{suc} \AgdaNumber{2} to \AgdaNumber{1}:

\begin{align*}
\mathbf{3} \xrightarrow[× 3 + 1]{\mod 2 = 1} 10 &\xrightarrow[/ 2]{\mod 2 = 0} 5 \xrightarrow[× 3 + 1]{\mod 2 = 1} 16 \xrightarrow[/ 2]{\mod 2 = 0} 8 \\
⋯ &\xrightarrow[/ 2]{\mod 2 = 0} 4 \xrightarrow[/ 2]{\mod 2 = 0} 2 \xrightarrow[/ 2]{\mod 2 = 0} \mathbf{1}
\end{align*}

\begin{code}
  Collatz‿2+1 : Collatz 2
  Collatz‿2+1 = 7 , refl
\end{code}





\chapter{Gauss formula\label{ch:Gauss}}

This Chapter presents a proof of the Gauss formula and a variation thereof for odd natural numbers. Both proofs use Σ-syntax and lemmas from the \AgdaModule{Bigop} module. In the second proof, the predicate \AgdaDatatype{Odd} and filters are used.

\AgdaHide{
\begin{code}
module Gauss where

  open import Bigop
  import Bigop.Properties.SemiringWithoutOne

  open import Algebra

  open import Function

  open import Data.List.Base
  open import Data.Unit hiding (setoid)

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Relation.Binary.PropositionalEquality as P
  import Relation.Binary.EqReasoning as EqR
\end{code}
}

\AgdaHide{
\begin{code}
  module GaussFormula where

    open import Data.Nat.Base using (zero; suc; _∸_)
    open import Data.Nat.Properties using (commutativeSemiring)
    open import Data.Product using (proj₁; proj₂)
    open CommutativeSemiring commutativeSemiring renaming (Carrier to ℕ)

    module Σ = Bigop.Properties.SemiringWithoutOne semiringWithoutOne
    open import Bigop.Interval.Nat
    open import Bigop.Interval.Properties.Nat

    open Fold +-monoid using (fold; Σ-syntax)
    open P.≡-Reasoning
\end{code}
}

\section{Gauss formula}

In this Section, we show a pen-and-paper proof of the equation \[2 · \sum_{i = 0}^n i = n · (n + 1)\] followed by a formal proof using definitions and lemmas from the \AgdaModule{Bigop} module. The proof proceeds induction over \AgdaBound{n}. The base case holds trivially as \[2 · \sum_{i = 0}^0 i = 0 = 0 · (0 + 1)\]

The induction hypothesis is \[ 2 · \sum_{i ← 0 … n} i = n · (n + 1) \]

and the induction step works as follows:
\begin{align}
2 · \sum_{i ← 0 … 1 + n} i
&= 2 · \left( \left( \sum_{i ← 0 … n} i \right) + 1 + n \right) \\
&= \left( 2 · \sum_{i ← 0 … n} i \right) + \left( 2 · (1 + n) \right) \\
&= n · (1 + n) + 2 · (1 + n) \\
&= 2 · (1 + n) + n · (1 + n) \\
&= (2 + n) · (1 + n) \\
&= (1 + n) · (2 + n)
\end{align}

In Agda, using Σ-syntax, the theorem
\begin{gather*}
∀ n.\quad 2 · \sum_{i = 0}^n i = n · (n + 1) \\
\intertext{is expressed as}
\text{\AgdaSymbol{∀} \AgdaBound{n} \AgdaSymbol{→} \AgdaNumber{2} \AgdaFunction{*} \AgdaSymbol{(}\AgdaFunction{Σ[} \AgdaBound{i} \AgdaSymbol{←} \AgdaNumber{0} \AgdaFunction{…} \AgdaBound{n} \AgdaFunction{]} \AgdaBound{i}\AgdaSymbol{)} \AgdaDatatype{≡} \AgdaBound{n} \AgdaFunction{*} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{n}\AgdaSymbol{)}}
\end{gather*}

Proof by natural number induction over \AgdaBound{n} translates to pattern matching on this argument in Agda. The base case is \(\AgdaBound{n} = \AgdaInductiveConstructor{zero}\); the induction step is given as the right-hand side of the pattern \AgdaInductiveConstructor{suc} \AgdaBound{n}.

In the induction step, we use equational reasoning (see \cref{ssc:Equational-reasoning}) to transform the equation step by step. Each step is annotated with the corresponding equation in the proof shown above.
The lemmas used to justify the transformation are:
\begin{align*}
\text{\AgdaField{proj₁} \AgdaFunction{distrib}}\;&:\;\text{\AgdaSymbol{∀} \AgdaBound{x} \AgdaBound{y} \AgdaBound{z} \AgdaSymbol{→} \AgdaBound{x} \AgdaFunction{*} \AgdaSymbol{(}\AgdaBound{y} \AgdaFunction{+} \AgdaBound{z}\AgdaSymbol{)} \AgdaDatatype{≡} \AgdaBound{x} \AgdaFunction{*} \AgdaBound{y} \AgdaFunction{+} \AgdaBound{x} \AgdaFunction{*} \AgdaBound{z}} \\
\text{\AgdaFunction{+-comm}}\;&:\;\text{\AgdaSymbol{∀} \AgdaBound{x} \AgdaBound{y} \AgdaSymbol{→} \AgdaBound{x} \AgdaFunction{+} \AgdaBound{y} \AgdaDatatype{≡} \AgdaBound{y} \AgdaFunction{+} \AgdaBound{x}} \\
\text{\AgdaFunction{*-comm}}\;&:\;\text{\AgdaSymbol{∀} \AgdaBound{x} \AgdaBound{y} \AgdaSymbol{→} \AgdaBound{x} \AgdaFunction{*} \AgdaBound{y} \AgdaDatatype{≡} \AgdaBound{y} \AgdaFunction{*} \AgdaBound{x}} \\
\text{\AgdaFunction{lemma}}\;&:\;\text{\AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…} \AgdaInductiveConstructor{suc} \AgdaBound{n} \AgdaFunction{]} \AgdaBound{i} \AgdaDatatype{≡} \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…} \AgdaBound{n} \AgdaFunction{]} \AgdaBound{i} \AgdaFunction{+} \AgdaInductiveConstructor{suc} \AgdaBound{n}}
\end{align*}

In step (C.3), the induction hypothesis \AgdaFunction{proof} \AgdaBound{n} is used.

\begin{code}
    proof : ∀ n → 2 * (Σ[ i ← 0 … n ] i) ≡ n * (suc n)
    proof zero = P.refl -- trivial base case
    proof (suc n) =
      begin
        2 * (Σ[ i ← 0 … suc n ] i)
{- C.1 -}  ≡⟨ P.cong (_*_ 2) lemma ⟩
        2 * (Σ[ i ← 0 … n ] i + suc n)
{- C.2 -}  ≡⟨ proj₁ distrib 2 (Σ[ i ← 0 … n ] i) (suc n) ⟩
        2 * (Σ[ i ← 0 … n ] i) + 2 * suc n
{- C.3 -}  ≡⟨ P.cong₂ _+_ (proof n) P.refl ⟩
        n * suc n + 2 * suc n
{- C.4 -}  ≡⟨ +-comm (n * suc n) (2 * suc n) ⟩
        2 * suc n + n * suc n
{- C.5 -}  ≡⟨ P.sym (proj₂ distrib (suc n) 2 n) ⟩
        (2 + n) * suc n
{- C.6 -}  ≡⟨ *-comm (2 + n) (suc n) ⟩
        suc n * (suc (suc n))
      ∎
      where
        lemma : Σ[ i ← 0 … suc n ] i ≡ Σ[ i ← 0 … n ] i + suc n
        lemma =
          begin
            Σ[ i ← 0 … suc n ] i       ≡⟨ P.cong (fold id) (upFrom-last 1 n) ⟩
            Σ[ i ← 0 … n ∷ʳ suc n ] i  ≡⟨ Σ.last id (suc n) (0 … n) ⟩
            Σ[ i ← 0 … n ] i + suc n
          ∎
\end{code}

\section{Odd Gauss formula}

\AgdaHide{
\begin{code}
  module OddGauss where

    open import Data.Nat.Properties.Simple using (+-suc)
    open import Data.List.Base
    open import Data.Empty
    open import Relation.Nullary.Decidable

    open import Data.Nat.Base hiding (fold)
    open import Data.Nat.Properties using (commutativeSemiring)
    open CommutativeSemiring commutativeSemiring hiding (_+_; _*_)

    module Σ = Bigop.Properties.SemiringWithoutOne semiringWithoutOne
    open import Bigop.Interval.Nat
    open import Bigop.Interval.Properties.Nat
    open import Bigop.Filter
    open import Bigop.Filter.Properties

    open Fold +-monoid using (fold; Σ-syntax)
    open P.≡-Reasoning

    open import Relation.Unary
\end{code}
}

A variant of the Gauss formula is the equation \[ ∀ n.\quad\sum_{\substack{i ← 0 … 2n \\ \text{\(i\) odd}}} i = n² \]

which using Σ-syntax and the filter function \AgdaFunction{\_∥\_} can be written as follows in Agda: \[
\text{\AgdaSymbol{∀} \AgdaBound{n} \AgdaSymbol{→} \AgdaFunction{Σ[} \AgdaBound{i} \AgdaFunction{←} \AgdaNumber{0} \AgdaFunction{…+} \AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaBound{n} \AgdaFunction{+} \AgdaBound{n}\AgdaSymbol{)} \AgdaFunction{∥} \AgdaFunction{odd} \AgdaFunction{]} \AgdaBound{i} \AgdaDatatype{≈} \AgdaBound{n} \AgdaFunction{*} \AgdaBound{n}}
\]

The lemma \AgdaFunction{extract} brings the list into a form more amenable to induction. It states that the list of odd numbers from zero up to but not including \(2n + 3\) equals the list of odd numbers from zero up to but not including \(2n + 1\) with \(2n + 1\) appended to it.

In the first step (A) the auxiliary lemma \AgdaFunction{3suc} is applied to rewrite \AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaBound{n} \AgdaPrimitive{+} \AgdaInductiveConstructor{suc} \AgdaBound{n}\AgdaSymbol{)} to \AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaBound{n} \AgdaPrimitive{+} \AgdaBound{n}\AgdaSymbol{)))}. Next (B) \AgdaFunction{upFrom-last} extracts the last element of the list \AgdaNumber{0} \AgdaFunction{…+} \AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaBound{n} \AgdaFunction{+} \AgdaBound{n}\AgdaSymbol{))}. Step (C) uses \AgdaFunction{last-no} and
\[
\text{\AgdaFunction{even→¬odd} \AgdaSymbol{(}\AgdaInductiveConstructor{ss-even} \AgdaSymbol{(}\AgdaFunction{2n-even} \AgdaBound{n}\AgdaSymbol{))}}\;\AgdaSymbol{:}\;\text{\AgdaFunction{¬} \AgdaDatatype{Odd} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaBound{n} \AgdaFunction{+} \AgdaBound{n}\AgdaSymbol{)))}}
\]
to show that \AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaBound{n} \AgdaFunction{+} \AgdaBound{n}\AgdaSymbol{))} is filtered out. In step (D) we again extract the last element of the list, \AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaBound{n} \AgdaFunction{+} \AgdaBound{n}\AgdaSymbol{)}. Lastly (E), we use \AgdaFunction{last-yes} and
\[
\text{\AgdaFunction{even+1} \AgdaSymbol{(}\AgdaFunction{2n-even} \AgdaBound{n}\AgdaSymbol{)}}\;\AgdaSymbol{:}\;\text{\AgdaDatatype{Odd} \AgdaSymbol{(}\AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaBound{n} \AgdaFunction{+} \AgdaBound{n}\AgdaSymbol{))}}
\]
to show that \AgdaInductiveConstructor{suc} \AgdaSymbol{(}\AgdaBound{n} \AgdaFunction{+} \AgdaBound{n} is odd, which allows us to take this element out of the filter.

\begin{code}
    extract : ∀ n →  0 … (suc n + suc n) ∥ odd ≡
                     0 … (n + n) ∥ odd ∷ʳ suc (n + n)
    extract n =
      begin
        0 … (suc n + suc n) ∥ odd
{- A -}   ≡⟨ P.cong (flip _∥_ odd ∘ _…_ 0) (+-suc (suc n) n) ⟩
        0 … (suc (suc (n + n))) ∥ odd
{- B -}   ≡⟨ P.cong (flip _∥_ odd) (upFrom-last 0 (suc (suc (n + n)))) ⟩
        0 … (suc (n + n)) ∷ʳ suc (suc (n + n)) ∥ odd
{- C -}   ≡⟨ last-no  (0 … (suc (n + n))) (suc (suc (n + n))) odd
                      (even→¬odd (ss-even (2n-even n))) ⟩
        0 … (suc (n + n)) ∥ odd
{- D -}   ≡⟨ P.cong (flip _∥_ odd) (upFrom-last 0 (suc (n + n))) ⟩
        0 … (n + n) ∷ʳ suc (n + n) ∥ odd
{- E -}   ≡⟨ last-yes  (0 … (n + n)) (suc (n + n)) odd
                       (even+1 (2n-even n)) ⟩
        0 … (n + n) ∥ odd ∷ʳ suc (n + n)
      ∎
\end{code}

The proof of the odd Gauss equation again works by natural number induction on \AgdaBound{n}, with a trivial base case for zero. In the induction step, we first rewrite the index list using \AgdaFunction{extract} (F). Then \AgdaFunction{Σ.last} is used to move the last element of the list out of the sum (G). In step (H) we use the induction hypothesis. The remainder of the proof just rewrites the algebraic expression into the required form.

\begin{code}
    proof : ∀ n → Σ[ i ← 0 … (n + n) ∥ odd ] i ≡ n * n
    proof zero = P.refl
    proof (suc n) =
      begin
        Σ[ i ← 0 … (suc n + suc n) ∥ odd ] i
{- F -}   ≡⟨ P.cong (fold id) (extract n)⟩
        Σ[ i ← 0 … (n + n) ∥ odd ∷ʳ suc (n + n) ] i
{- G -}   ≡⟨ Σ.last id (suc (n + n)) (0 … (n + n) ∥ odd) ⟩
        Σ[ i ← 0 … (n + n) ∥ odd ] i + suc (n + n)
{- H -}   ≡⟨ +-cong (proof n) refl ⟩

        n * n + suc (n + n)  ≡⟨ +-cong (refl {x = n * n}) (sym (+-suc n n)) ⟩
        n * n + (n + suc n)  ≡⟨ sym $ +-assoc (n * n) n (suc n) ⟩
        (n * n + n) + suc n  ≡⟨ +-cong (+-comm (n * n) _) refl ⟩
        suc n * n + suc n    ≡⟨ +-comm (suc n * n) _ ⟩
        suc n + suc n * n    ≡⟨ +-cong (refl {x = suc n}) (*-comm (suc n) n) ⟩
        suc n * suc n
      ∎
\end{code}
% $

\chapter{Binomial Theorem\label{ch:Binom}}

In this Chapter, we use the \AgdaModule{Bigop} module to prove a special case of the binomial theorem (see, for example, equation 5.13 on page 163 in \textcite{graham_concrete_1994}): \[\sum_{k ← 0 … n-1} \binom{n}{k} · x^k = (1 + x)^n\]
We present a pen-and-paper proof first and then translate it into Agda.

\section{Pen-and-paper proof}

The proof works by natural number induction on \AgdaBound{n}. The base case with \(n = 0\) is trivial as \(\binom{n}{0} · x^0 = 1 = (1 + x)^n\). The induction step proceeds as follows:
\begin{align}
\sum_{k ← 0 … n + 1} \binom{n + 1}{k} · x^k
&= 1 + \sum_{k ← 1 … n + 1} \binom{n + 1}{k} · x^k \\
&= 1 + \left( \sum_{k ← 0 … n} \binom{n}{k} · x^{k+1} + \sum_{k ← 0 … n} \binom{n}{k + 1} · x^{k+1} \right) \\
&= \sum_{k ← 0 … n} \binom{n}{k} · x^{k+1} + \left( 1 + \sum_{k ← 0 … n} \binom{n}{k + 1} · x^{k+1} \right) \\
&= x · \sum_{k ← 0 … n} \binom{n}{k} · x^k + \sum_{k ← 0 … n} \binom{n}{k} · x^k \\
&= x · \sum_{k ← 0 … n} \binom{n}{k} · x^k + 1 · \sum_{k ← 0 … n} \binom{n}{k} · x^k \\
&= (x + 1) · \sum_{k ← 0 … n} \binom{n}{k} · x^k \\
&= (1 + x)^{1 + n}
\end{align}
Here the last step uses the induction hypothesis, \(\sum_{k ← 0 … n} \binom{n}{k} · x^k = (1 + x)^n\).

\section{Definitions}

Since the Agda standard library does not currently define exponentials and binomials for natural numbers, we start by writing down their inductive definitions:

\AgdaHide{
\begin{code}
module BinomialTheorem where

  open import Bigop
  open import Bigop.Interval.Properties.Nat
  import Bigop.Properties.SemiringWithoutOne

  open import Algebra
  open import Data.Nat.Base using (_∸_; zero; suc)
  open import Data.Nat.Properties using (commutativeSemiring)
  open import Data.Nat.Properties.Simple using (+-suc)
  open import Function
  open import Relation.Binary.PropositionalEquality as P using (_≡_)
  open P.≡-Reasoning

  open CommutativeSemiring commutativeSemiring hiding (Carrier)
  module Σ = Bigop.Properties.SemiringWithoutOne semiringWithoutOne
  open Fold +-monoid using (fold; Σ-syntax)

  open import Data.List
  open import Data.Product using (proj₁; proj₂)

  open import Level renaming (zero to lzero; suc to lsuc)

  open import Bigop.Interval.Nat

  infixr 8 _^_
\end{code}
}

\begin{code}
  _^_ : ℕ → ℕ → ℕ
  x ^ 0      = 1
  x ^ suc n  = x * x ^ n

  _choose_ : ℕ → ℕ → ℕ
  _      choose  0      = 1
  0      choose  suc k  = 0
  suc n  choose  suc k  = n choose k + n choose (suc k)
\end{code}
Additionally we define a shorthand \AgdaFunction{f} for the general form of the function we will be manipulating within the sum:

\begin{code}
  f : ℕ → ℕ → ℕ → ℕ
  f x n k = n choose k * x ^ k
\end{code}

\section{Lemmas}

In this Section we prove the lemmas used in the final proof of the binomial theorem.

\AgdaFunction{split} justifies the step from (D.1) to (D.2):
\[ \sum_{k ← 1 … n + 1} \binom{n + 1}{k} · x^k = \left( \sum_{k ← 0 … n} \binom{n}{k} · x^{k+1} + \sum_{k ← 0 … n} \binom{n}{k + 1} · x^{k+1} \right)
\] by shifting the values of its index list down by one and splitting the sum into two. In the actual proof, the addition with \(1\) is taken care of using reflexivity and congruence of addition.
% \footnote{This lemma and the following ones may seem arbitrary---there is no obvious connection to the binomial theorem other than the fact that the equations contain binomials and exponentials. The reason is that the lemmas were simply factored out of the main proof.}

\begin{code}
  split : ∀ x n →  Σ[ k ← 1 … suc n ] (suc n) choose k * x ^ k ≡
                   Σ[ k ← 0 … n ] n choose k * x ^ (suc k)
                   + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k)
  split x n =
    begin
      Σ[ k ← 1 … suc n ] (suc n) choose k * x ^ k
        ≡⟨ sym $ P.cong (fold (f x (suc n))) (upFrom-suc 0 (suc n)) ⟩
      Σ[ k ← map suc (0 … n) ] (suc n) choose k * x ^ k
        ≡⟨ sym $ Σ.map′ (f x (suc n)) suc (0 … n) (λ _ _ → refl) ⟩
      Σ[ k ← 0 … n ] (n choose k + n choose (suc k)) * x ^ (suc k)
        ≡⟨ Σ.cong  {f = λ k → (n choose k + n choose (suc k)) * x ^ (suc k)}
                   (0 … n) P.refl
                   (λ k → distribʳ (x ^ (suc k)) (n choose k) _) ⟩
      Σ[ k ← 0 … n ] (  n choose k * x ^ (suc k)
                        + n choose (suc k) * x ^ (suc k))
         ≡⟨ sym $ Σ.merge  (λ k → n choose k * x ^ (suc k)) (λ k → f x n (suc k))
                           (0 … n) ⟩
      Σ[ k ← 0 … n ] n choose k * x ^ (suc k)
         + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k)
    ∎
\end{code}
% $
\AgdaFunction{+-reorder} simply re-arranges three summands, as it is done in the pen-and-paper proof between (D.2) and (D.3):
\[ 1 + \left( \sum_{k ← 0 … n} \binom{n}{k} · x^{k+1} + \sum_{k ← 0 … n} \binom{n}{k + 1} · x^{k+1} \right) = \sum_{k ← 0 … n} \binom{n}{k} · x^{k+1} + \left( 1 + \sum_{k ← 0 … n} \binom{n}{k + 1} · x^{k+1} \right)
\] We also prove \AgdaFunction{*-reorder}, which proves that the same transformation holds for multiplication. This auxiliary lemma is used in \AgdaFunction{left-distr} (below).

\begin{code}
  +-reorder : ∀ x y z → x + (y + z) ≡ y + (x + z)
  +-reorder x y z =
    begin
      x + (y + z)  ≡⟨ sym $ +-assoc x y z ⟩
      (x + y) + z  ≡⟨ +-cong (+-comm x y) refl ⟩
      (y + x) + z  ≡⟨ +-assoc y x z ⟩
      y + (x + z)
    ∎

  *-reorder : ∀ x y z → x * (y * z) ≡ y * (x * z)
  *-reorder x y z =
    begin
      x * (y * z)  ≡⟨ sym $ *-assoc x y z ⟩
      (x * y) * z  ≡⟨ *-cong (*-comm x y) refl ⟩
      (y * x) * z  ≡⟨ *-assoc y x z ⟩
      y * (x * z)
    ∎
\end{code}
The lemma \AgdaFunction{left-distr} uses \AgdaFunction{*-reorder} and the left-distributivity law for sums (\AgdaFunction{Σ.distrˡ}) to pull a factor \AgdaBound{x} out of the exponential in the sum. It provides justification for going from the left-hand side of the outer addition in (D.3) to the left-hand side of the addition in (D.4):
\[ \sum_{k ← 0 … n} \binom{n}{k} · x^{k+1} = x · \sum_{k ← 0 … n} \binom{n}{k} · x^k
\]

\begin{code}
  left-distr : ∀ x n →  Σ[ k ← 0 … n ] n choose k * x ^ (suc k) ≡
                        x * (Σ[ k ← 0 … n ] n choose k * x ^ k)
  left-distr x n =
    begin
      Σ[ k ← 0 … n ] n choose k * x ^ (suc k)
        ≡⟨ Σ.cong (0 … n) P.refl (λ k → *-reorder (n choose k) x (x ^ k)) ⟩
      Σ[ k ← 0 … n ] x * (n choose k * x ^ k)
        ≡⟨ sym $ Σ.distrˡ (f x n) x (0 … n) ⟩
      x * (Σ[ k ← 0 … n ] n choose k * x ^ k)
    ∎
\end{code}
% $
The auxiliary lemma \AgdaFunction{choose-lt} is equivalent to \AgdaBound{p} \AgdaDatatype{<} \AgdaBound{q} \AgdaSymbol{→} \AgdaBound{p} \AgdaFunction{choose} \AgdaBound{q} \AgdaDatatype{≡} \AgdaNumber{0}, but this is the form in which it is used in \AgdaFunction{choose-suc}. The keyword \AgdaKeyword{mutual} allows \AgdaFunction{choose-lt} to be defined in terms of \AgdaFunction{choose-lt′} and vice versa.
\AgdaFunction{choose-lt} is required for \AgdaFunction{choose-suc}, which in turn is used in \AgdaFunction{shift} (below).

\begin{code}
  mutual
    choose-lt : ∀ m n → n choose (suc m + n) ≡ 0
    choose-lt m zero     = P.refl
    choose-lt m (suc n)  = choose-lt′ m n ⟨ +-cong ⟩ choose-lt′ (suc m) n

    choose-lt′ : ∀ m n → n choose (m + suc n) ≡ 0
    choose-lt′ m n =
      begin
        n choose (m + suc n)  ≡⟨ P.refl ⟨ P.cong₂ _choose_ ⟩ +-suc m n ⟩
        n choose suc (m + n)  ≡⟨ choose-lt m n ⟩
        0
      ∎

  choose-suc : ∀ x n →  Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k) ≡
                        Σ[ k ← 1 … n ] n choose k * x ^ k
  choose-suc x n  =
    begin
      Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k)
        ≡⟨ Σ.map′ (f x n) suc (0 … n) (λ _ _ → refl) ⟩
      Σ[ k ← map suc (0 … n) ] n choose k * x ^ k
        ≡⟨ P.cong (fold $ f x n) (upFrom-suc 0 (suc n)) ⟩
      Σ[ k ← 1 … suc n ] n choose k * x ^ k
        ≡⟨ P.cong (fold $ f x n) (upFrom-last 1 n) ⟩
      Σ[ k ← (1 … n) ∷ʳ (suc n) ] n choose k * x ^ k
        ≡⟨ Σ.last (f x n) (suc n) (1 … n) ⟩
      (Σ[ k ← 1 … n ] n choose k * x ^ k) + n choose (suc n) * x ^ (suc n)
        ≡⟨ +-cong  (refl {x = Σ[ k ← 1 … n ] f x n k})
                   (choose-lt 0 n ⟨ *-cong ⟩ refl ⟨ trans ⟩ zeroˡ n) ⟩
      (Σ[ k ← 1 … n ] n choose k * x ^ k) + 0
        ≡⟨ proj₂ +-identity _ ⟩
      Σ[ k ← 1 … n ] n choose k * x ^ k
    ∎
\end{code}
Our final lemma \AgdaFunction{shift} justifies the equality between the right-hand side of the outer addition in (D.3) and the right-hand side of the outer addition in (D.4):
\[ \left( 1 + \sum_{k ← 0 … n} \binom{n}{k + 1} · x^{k+1} \right) = \sum_{k ← 0 … n} \binom{n}{k} · x^k
\]

\begin{code}
  shift : ∀ x n →  1 + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k)
                   ≡ Σ[ k ← 0 … n ] n choose k * x ^ k
  shift x n =
    begin
      1 + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k)
        ≡⟨ (refl {x = 1}) ⟨ +-cong ⟩  (choose-suc x n) ⟩
      1 + Σ[ k ← 1 … n ] n choose k * x ^ k
        ≡⟨ refl ⟩
      Σ[ k ← 0 ∷ (1 … n) ] n choose k * x ^ k
        ≡⟨ P.cong (fold $ f x n) (upFrom-head 0 n) ⟩
      Σ[ k ← 0 … n ] n choose k * x ^ k
    ∎
\end{code}
% $

\section{Proof}

The following Agda proof is annotated by the corresponding steps in the pen-and-paper proof presented at the beginning of the chapter.

\begin{code}
  proof : ∀ x n → Σ[ k ← 0 … n ] n choose k * x ^ k ≡ (suc x) ^ n
  proof x zero    = refl
  proof x (suc n) =
    begin
      1 + Σ[ k ← 1 … suc n ] (suc n) choose k * x ^ k
{- D.1 -}  ≡⟨ refl {x = 1} ⟨ +-cong ⟩ (split x n) ⟩
      1 + (  Σ[ k ← 0 … n ] n choose k * x ^ (suc k)
             + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k))
{- D.2 -}  ≡⟨ +-reorder 1 (Σ[ k ← 0 … n ] n choose k * x ^ (suc k)) _ ⟩
      Σ[ k ← 0 … n ] n choose k * x ^ (suc k)
      + (1 + Σ[ k ← 0 … n ] n choose (suc k) * x ^ (suc k))
{- D.3 -}  ≡⟨ left-distr x n ⟨ +-cong ⟩ shift x n ⟩
      x *  (Σ[ k ← 0 … n ] n choose k * x ^ k) +
           (Σ[ k ← 0 … n ] n choose k * x ^ k)
{- D.4 -}  ≡⟨ refl {x = x * _} ⟨ +-cong ⟩ sym (proj₁ *-identity _) ⟩
      x *  (Σ[ k ← 0 … n ] n choose k * x ^ k) +
      1 *  (Σ[ k ← 0 … n ] n choose k * x ^ k)
{- D.5 -}  ≡⟨ sym $ distribʳ _ x 1 ⟩
      (x + 1) * (Σ[ k ← 0 … n ] n choose k * x ^ k)
{- D.6 -}  ≡⟨ +-comm x 1 ⟨ *-cong ⟩ proof x n ⟩
      (suc x) ^ (suc n)
    ∎
\end{code}
% $








\chapter{Additional proofs}

\section{Arrow-pair isomorphism\label{sc:Curry}}

\AgdaHide{
\begin{code}
module Curry where
  open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

  open import Data.Nat hiding (_⊔_; _*_)
  open import Data.Nat.DivMod
  open import Data.Product hiding (∃; curry; uncurry)
  open import Relation.Binary.PropositionalEquality
\end{code}
}
The functions \AgdaFunction{curry} \AgdaSymbol{:} (\AgdaBound{A} \AgdaSymbol{→} \AgdaBound{B} \AgdaSymbol{→} \AgdaBound{C}) \AgdaSymbol{→} (\AgdaBound{A} \AgdaSymbol{×} \AgdaBound{B} \AgdaSymbol{→} \AgdaBound{C}) and \AgdaFunction{uncurry} \AgdaSymbol{:} (\AgdaBound{A} \AgdaSymbol{×} \AgdaBound{B} \AgdaSymbol{→} \AgdaBound{C}) \AgdaSymbol{→} (\AgdaBound{A} \AgdaSymbol{→} \AgdaBound{B} \AgdaSymbol{→} \AgdaBound{C}) are easily defined:\footnote{It is also possible to write \AgdaFunction{curry} and \AgdaFunction{uncurry} for dependent pairs (\AgdaDatatype{Σ}).}

\begin{code}
  curry : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → B → C) → (A × B → C)
  curry f (x , y) = f x y

  uncurry : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A × B → C) → (A → B → C)
  uncurry f x y = f (x , y)
\end{code}
In order to show that \AgdaFunction{curry} and \AgdaFunction{uncurry} constitute an isomorphism, we prove that they are inverses of each other:

\begin{code}
  uncurry∘curry :  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                   (f : A → B → C) (x : A) (y : B) →
                   f x y ≡ uncurry (curry f) x y
  uncurry∘curry f x y = refl

  curry∘uncurry :  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                   (f : A × B → C) (x : A) (y : B) →
                   f (x , y) ≡ curry (uncurry f) (x , y)
  curry∘uncurry f x y = refl
\end{code}
Thus \AgdaDatatype{A} \AgdaSymbol{→} \AgdaDatatype{B} \AgdaSymbol{→} \AgdaPrimitiveType{Set} and \AgdaDatatype{A} \AgdaSymbol{×} \AgdaDatatype{B} \AgdaSymbol{→} \AgdaPrimitiveType{Set} are isomorphic and we can use them interchangeably.

\newpage

\section{Equality of left and right fold\label{ch:foldl-foldr}}

\AgdaHide{
\begin{code}
module FoldlFoldr where
  open import Data.List
  open import Data.Product using (proj₁; proj₂)
  import Relation.Binary.EqReasoning as EqR
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)

  open import Algebra
  import Bigop.Core as Core
\end{code}
}

\AgdaFunction{foldr≡foldl} shows that for any list, the right- and left-fold over that list evaluate to the same value if the binary operator and identity of a monoid are supplied as the first and second argument in either case.

\begin{code}
  module Fold {c ℓ} (M : Monoid c ℓ) where
    open Monoid M renaming (Carrier to R)
    open Core.Fold M using (fold)
    open EqR setoid

    -- Lemmas
    foldl-cong : ∀ x y xs → x ≈ y → foldl _∙_ x xs ≈ foldl _∙_ y xs
    foldl-cong x y []        x≈y = x≈y
    foldl-cong x y (z ∷ zs)  x≈y = foldl-cong (x ∙ z) (y ∙ z) zs (∙-cong x≈y refl)

    foldl-step : ∀ x xs → x ∙ foldl _∙_ ε xs ≈ foldl _∙_ (ε ∙ x) xs
    foldl-step x [] = begin
      x ∙ ε  ≈⟨ proj₂ identity x ⟩
      x      ≈⟨ sym (proj₁ identity x) ⟩
      ε ∙ x  ∎
    foldl-step x (y ∷ ys) = begin
      x ∙ foldl _∙_ (ε ∙ y) ys    ≈⟨ ∙-cong refl (sym (foldl-step y ys)) ⟩
      x ∙ (y ∙ foldl _∙_ ε ys)    ≈⟨ sym (assoc x y _) ⟩
      (x ∙ y) ∙ foldl _∙_ ε ys    ≈⟨ foldl-step (x ∙ y) ys ⟩
      foldl _∙_ (ε ∙ (x ∙ y)) ys  ≈⟨ foldl-cong  (ε ∙ (x ∙ y)) (ε ∙ x ∙ y) ys
                                                 (sym (assoc ε x y)) ⟩
      foldl _∙_ (ε ∙ x ∙ y) ys    ∎

    -- The left- and right-fold over a list using a monoidal binary
    -- operator are equal.
    foldr≡foldl : (xs : List R) → foldr _∙_ ε xs ≈ foldl _∙_ ε xs
    foldr≡foldl []        = refl
    foldr≡foldl (x ∷ xs)  = begin
      x ∙ foldr _∙_ ε xs    ≈⟨ ∙-cong refl (foldr≡foldl xs) ⟩
      x ∙ foldl _∙_ ε xs    ≈⟨ foldl-step x xs ⟩
      foldl _∙_ (ε ∙ x) xs  ∎
\end{code}

\newpage

\section{Extensional equality with reducebig\label{sc:Reducebig}}

The \texttt{bigop} module for Coq defines an evaluation function for big operators called \texttt{reducebig}.\footnote{A syntax-highlighted and clickable version of this module's source code is available here: \url{http://ssr.msr-inria.inria.fr/doc/mathcomp-1.5/MathComp.bigop.html}.} Here we translate it into an Agda function \AgdaFunction{reducebig} and show that its result is equal to evaluating our library's big operator function, \AgdaFunction{fold}.

\AgdaHide{
\begin{code}
open import Algebra

module Reducebig {c ℓ} (M : Monoid c ℓ) where
  import Bigop.Core as Core
  open import Bigop.Filter

  open import Data.Bool.Base
  open import Data.List
  open import Data.Product using (proj₁; proj₂)
  open import Relation.Nullary using (yes; no)
  open import Relation.Nullary.Decidable using (⌊_⌋)
  open import Relation.Unary using (Pred; Decidable)
  import Relation.Binary.EqReasoning as EqR
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)
\end{code}
}

\begin{code}
  open Monoid M renaming (Carrier to R)
  open Core.Fold M using (fold)
  open EqR setoid

  -- `reducebig` is how big operators are evaluated in Coq's bigop module.
  reducebig :  ∀ {i p} {I : Set i} {P : Pred I p} →
               (I → R) → Decidable P → List I → R
  reducebig f p = foldr (λ i acc → if ⌊ p i ⌋ then f i ∙ acc else acc) ε

  -- `reducebig` and Bigop.Core.Fold.fold are extensionally equal
  equivalent :  ∀ {i p} {I : Set i} {P : Pred I p} →
                (f : I → R) (p : Decidable P) (is : List I) →
                reducebig f p is ≡ fold f (is ∥ p)
  equivalent f p []        = P.refl
  equivalent f p (i ∷ is)  with p i
  ... | yes pi  = P.cong (_∙_ (f i)) (equivalent f p is)
  ... | no ¬pi  = equivalent f p is
\end{code}

%TC:endignore
\end{document}
