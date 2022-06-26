\begin{code}
{-# LANGUAGE LambdaCase, StandaloneDeriving #-}

module Posts.Variables where
import qualified Data.List as List
\end{code}

\title{Compiling to Categories: Variables}

Lambda calculus is embodied by cartesian closed categories. Translations between
lambda calculus representations (such as a compiler) should be functors that preserve
the cartesian closed structure.

There is a subset of machine code programs that correspond to lambda calculus programs.
This subset should itself form a cartesian closed category. And the translation from
lambda calculus to lambda-calculus-as-machine-code should be a cartesian closed functor.

\section{Preliminaries}

\subsection{Terms}

\begin{code}
data Expr
\end{code}

Variables: \(x\), \(y\), \(z\)

\begin{code}
  = Var String
\end{code}

Abstraction: \(\mathtt{\lambda (} x \; \mathtt{:} \; A \mathtt{).} \; e\)

\begin{code}
  | Lam String Type Expr
\end{code}

Application: \(f \; x\)

\begin{code}
  | App Expr Expr
\end{code}

Unit: \(\mathtt{()}\)

\begin{code}
  | Unit
\end{code}

Pairs: \(\mathtt{(} a \mathtt{,} b \mathtt{)}\)

\begin{code}
  | Pair Expr Expr
\end{code}

Projection: \(x\mathtt{.fst}\), \(x\mathtt{.snd}\)

\begin{code}
  | Fst Expr
  | Snd Expr
\end{code}

\subsection{Types}

\begin{code}
data Type
\end{code}

Functions: \(\mathtt{Fn} \; A \; B\)

\begin{code}
  = TFunc Type Type
\end{code}

Unit: \(\mathtt{Unit}\)

\begin{code}
  | TUnit
\end{code}

Pairs: \(\mathtt{Pair} \; A \; B\)

\begin{code}
  | TPair Type Type
\end{code}

\subsection{Contexts}

\begin{code}
data Context
\end{code}

The empty context: \(\epsilon\)

\begin{code}
  = Empty
\end{code}

Context extension: \(\Gamma , T\)

\begin{code}
  | Snoc Context Type
\end{code}

Finitely-sized contexts: \([ T_1, T_2, \dots, T_n ]\)

\begin{code}
fromList :: [Type] -> Context
fromList = foldl Snoc Empty
\end{code}

\subsection{The Category of Contexts}

Contexts are the objects. An arrow \(\Gamma \rightarrow \Delta\) consists of
terms \(x_1, x_2, \dots, x_n\) such that \(\Gamma \vdash x_i : T_i\) for each \(T_i \in \Delta\).

Each term of type \(T\) corresponds to an arrow \(\Gamma \rightarrow [ T ]\), where \(\Gamma\)
represents the term's free variables. I'll call these arrows-targeting-singleton-contexts "term arrows".

\subsubsection{Products}

A context \(\Gamma\) of size \(n\) is the product of \(n\) singleton contexts;
one for each element of \(\Gamma\).

Pairing terms introduces products, i.e.

\[
\frac
  {
    a : \Gamma \rightarrow [ A ] \;\;\;\;\;\;
    b : \Gamma \rightarrow [ B ] \;\;\;\;\;\;
    c : \Gamma \rightarrow [ C ]
  }
  {a, b, c : \Gamma \rightarrow [A, B, C]}
\]

There's a family of projection arrows \(index_n : \Gamma \rightarrow [ T_n ]\)
that 'focus' on each element of the context.

\subsubsection{Terminal Object}

\([\mathtt{Unit}]\), due to the typing rule

\[
\frac
  {}
  {\Gamma \vdash \mathtt{()} : \mathtt{Unit}}

\;\;

\text{(t-unit)}
\]

which gives rise to the arrow \(unit : \Gamma \rightarrow [ \mathtt{Unit} ]\).

\subsubsection{Exponentials}

\([ \mathtt{Fn} \; A \: B ]\)

The abstraction arrow is derived from the typing rule for abstraction

\[
\frac
  {\Gamma , A \vdash e : B}
  {\Gamma \vdash \mathtt{\lambda (} x : A \mathtt{).} \; e : \mathtt{Fn} \; A \; B}

\;\;

\text{(t-abs)}
\]

giving

\[
\frac
  {f : \Gamma , A \rightarrow [ B ]}
  {\lambda f : \Gamma \rightarrow [ \mathtt{Fn} \; A \; B ] }
\]
\]

We also have the arrow \(apply : [ \mathtt{Fn} \; A \; B , A ] \rightarrow [ B ]\).

\section{Translation}

We'll translate lambda calculus terms to arrows of a cartesion closed category, using
the category of contexts as a guide.

We start by defining the syntax of these arrows.

\subsection{Cartesian Closed Category Syntax}

\begin{code}
data CCC
\end{code}

\\

\[
id : A \rightarrow A
\]

\begin{code}
  = CId
\end{code}

\\

\[
\frac
  {f : A \rightarrow B \;\;\;\; g : B \rightarrow C}
  {g \circ f : A \rightarrow C}
\]

\begin{code}
  | CCompose CCC CCC
\end{code}

\\

\[
\frac
  {
    f_1 : X \rightarrow [ T_1 ]
    \;\;\;\; 
    f_2 : X \rightarrow [ T_2 ]
    \;\;\;\; 
    \dots
    \;\;\;\; 
    f_n : X \rightarrow [ T_n ]
  }
  {\langle f_1, f_2, \dots, f_n \rangle : A \rightarrow [ T_1, T_2, \dots, T_n ]}
\]

\begin{code}
  | CPair [CCC] 
\end{code}

\\

\[
\frac
  {}
  {index_0 : X, T \rightarrow [ T ]}

\;\;\;\;\;\;

\frac
  {index_n : X \rightarrow [ T ]}
  {index_{(n+1)} : X, T' \rightarrow [ T ]}
\]

\begin{code}
  | CIndex Int
\end{code}

\\

\[
\frac
  {f : X, A \rightarrow B}
  {\lambda f : X \rightarrow [ \mathtt{Fn} \; A \; B ]}
\]

\begin{code}
  | CAbs CCC
\end{code}

\\

\[
\frac
  {}
  {apply : [ \mathtt{Fn} \; A \; B, A ] \rightarrow B}
\]

\begin{code}
  | CApply
\end{code}

\subsubsection{Introduction and Elimination Forms}

\[
\frac
  {}
  {mkunit : [] \rightarrow [ \mathtt{Unit} ]}
\]

\begin{code}
  | CMkUnit
\end{code}

\\

\[
\frac
  {f : X \rightarrow Y}
  {letunit(f) : X, \mathtt{Unit} \rightarrow Y}
\]

\begin{code}
  | CLetUnit CCC
\end{code}

\\

\[
\frac
  {}
  {mkpair : [ A , B ] \rightarrow [ \mathtt{Pair} \; A \; B ]}
\]

\begin{code}
  | CMkPair
\end{code}

\\

\[
\frac
  {f : X, A, B \rightarrow Y}
  {letpair(f) : X, \mathtt{Pair} \; A \; B \rightarrow Y}
\]

\begin{code}
  | CLetPair CCC
\end{code}

\subsection{de Bruijn Indexing}

The de Bruijn translation takes a context-with-variable-names \(\Gamma\) (\(names\)) and term \(\Gamma \vdash expr : T\)
and produces a cartesian closed category arrow \(\Delta \rightarrow T\).


\begin{code}
translate_deBruijn :: [(String, Type)] -> Expr -> CCC
translate_deBruijn names expr =
  case expr of
    Var name ->
\end{code}

Variables: compute the index \(i\) corresponding to \(name\), producing an
arrow \(\Delta \rightarrow T_i\).

\begin{code}
      case List.findIndex ((name ==) . fst) names of
        Just index -> 
          CIndex index
        Nothing -> 
          error $ show name <> " not in scope"
\end{code}

\begin{code}
    Lam name ty body -> 
\end{code}

Lambdas: given \(body' : \Delta, A \rightarrow T\)

\begin{code}
      let body' = translate_deBruijn ((name, ty): names) body in
\end{code}

produce \(\lambda body' : \Delta \rightarrow T\).

\begin{code}
      CAbs body'
\end{code}

\begin{code}
    App f x -> 
\end{code}

Application: pair \(f' : \Delta \rightarrow [ \mathtt{Fn} \; A \; B\ ]\) with \(x' : \Delta \rightarrow [ A ]\),
giving \(\langle f' , x' \rangle : \Delta \rightarrow [ \mathtt{Fn} \; A \; B , A ]\)

\begin{code}
      let f' = translate_deBruijn names f in
      let x' = translate_deBruijn names x in
      let f'x' = CPair [f', x'] in
\end{code}

then apply with \(apply : [ \mathtt{Fn} \; A \; B , A ] \rightarrow [ B ]\), resulting in
\(apply \circ \langle f' , x' \rangle \).

\begin{code}
      CCompose CApply f'x'
\end{code}

\begin{code}
    Unit -> 
\end{code}

Unit: \(mkunit \circ \langle \rangle : \Delta \rightarrow [ \mathtt{Unit} ] \)

\begin{code}
      CCompose CMkUnit (CPair [])
\end{code}

\begin{code}
    Pair a b -> 
\end{code}

Pairs: pair the arrows \(a' : \Delta \rightarrow [ \mathtt{Fn} \; A \; B\ ]\) with \(b' : \Delta \rightarrow [ A ]\),
giving \(\langle a' , b' \rangle : \Delta \rightarrow [ A , B ]\)

\begin{code}
      let a' = translate_deBruijn names a in
      let b' = translate_deBruijn names b in
      let a'b' = CPair [a', b'] in
\end{code}

then construct the \(\mathtt{Pair}\) using \(mkpair\): \(mkpair \circ \langle a' , b' \rangle : \Delta \rightarrow [ \mathtt{Pair} \; A \; B ] \)

\begin{code}
      CCompose CMkPair a'b'
\end{code}

\begin{code}
    Fst a -> 
      CCompose (CLetPair $ CIndex 1) (translate_deBruijn names a)
\end{code}

\begin{code}
    Snd a ->
      CCompose (CLetPair $ CIndex 0) (translate_deBruijn names a)
\end{code}