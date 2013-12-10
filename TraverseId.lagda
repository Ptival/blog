\documentclass{article}
\usepackage{a4}
\usepackage{palatino}
\usepackage{natbib}
\usepackage{amsfonts}
\usepackage{stmaryrd}
\usepackage{upgreek}

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}
\newcommand{\T}[1]{\raisebox{0.02in}{\tiny\green{\textsc{#1}}}}

\newcommand{\us}[1]{\_\!#1\!\_}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"

%format → = "\blue{\rightarrow}"
%format ℕ = "\blue{\mathbb{N}}"
%format rewrite = "\mathkw{rewrite}"
%format constructor = "\mathkw{constructor}"
%format ? = "\orange{?}"
%format <> = "\diamond"
%format _<*>_ = "\purple{\_ \langle \ast \rangle \_}"
%format <*> = "\blue{\langle \ast \rangle}"
%format ~= = "\blue{\triangleq}"
%format fun = "\lambda"

\begin{document}

\title{Funification of matrix traversals}
\author{Valentin Robert}
\maketitle

While playing with Conor McBride's material for his summer school on dependently-typed metaprogramming, I was puzzled as to how easy it was to implement matrix transposition. I will detail here what goes on, as I find the insight slightly amusing.

First, some boilerplate code:

\begin{code}
module TraverseId where

open import Data.Nat
open import Function
\end{code}

We define standard length-indexed lists (usually named vectors), and related operations.

\begin{code}
data Vec (X : Set) : ℕ → Set where
  <>   :                           Vec X zero
  _,_  : {n : ℕ} → X → Vec X n → Vec X (suc n)

vec : forall {n X} → X → Vec X n
vec {zero}  x = <>
vec {suc n} x = x , vec x

vapp :  forall {n S T} → Vec (S → T) n → Vec S n → Vec T n
vapp <>       <>       = <>
vapp (f , fs) (x , xs) = f x , vapp fs xs
\end{code}

We now define applicative functors, along with two instances for the identity functor and the fixed-sized vector functor (you can think of it as a finite tabulation).

\begin{code}
record Applicative (F : Set → Set) : Set1 where
  infixl 2 _<*>_
  field
    pure    : forall {X} → X → F X
    _<*>_   : forall {S T} → F (S → T) → F S → F T
open Applicative {{...}} public

applicativeVec  : forall {n} → Applicative \ X → Vec X n
applicativeVec  = record { pure = vec; _<*>_ = vapp }

applicativeId : Applicative id
applicativeId = record { pure = id; _<*>_ = id }
\end{code}

We then proceed to define the traversable interface.

\begin{code}
record Traversable (F : Set → Set) : Set1 where
  field
    traverse : forall {G S T}{{AG : Applicative G}} →
               (S → G T) → F S → G (F T)
open Traversable {{...}} public
\end{code}

You can try to think of traverse's signature in these terms: given a G-effectful action transforming an element of S into an element of T, and a F-structure containing some elements of S, we can compute a G-effectful action building up a F-structure of elements of T. In some sense, we map the action into the structure, and then we fold the structure of actions into a structure of results.

Vectors of a given size are traversable:

\begin{code}
traversableVec : {n : ℕ} → Traversable \ X → Vec X n
traversableVec = record { traverse = vtr } where
  vtr : forall {n G S T}{{_ : Applicative G}} →
               (S → G T) → Vec S n → G (Vec T n)
  vtr        f <>        = pure <>
  vtr {{aG}} f (s , ss)  = pure {{aG}} _,_ <*> f s <*> vtr f ss
\end{code}

The given exercise at this point in the course was to implement matrix transposition. It was heavily hinted that this would be implemented as a traversal, so I let myself be guided by the types, and write the following, where the question mark stands for a hole, a placeholder for a term that you do not want to write yet:

\begin{spec}
transpose : forall {m n X} → Vec (Vec X m) n → Vec (Vec X n) m
transpose = traverse {!!}
\end{spec}

At that point, the type of the hole (the expected type of the term to be filled in place of the hole) was the following:

\begin{spec}
Goal: Vec .X .m → Vec .X .m
\end{spec}

Well, do I have just the right candidate for that type! Even Agsy, the automated program search tool shipped with Agda, knows what to put in that hole!

\begin{spec}
transpose : forall {m n X} → Vec (Vec X m) n → Vec (Vec X n) m
transpose = traverse id
\end{spec}

At that point though, the doubt builds in my mind. It seems to me that a traversal with the ineffectful identity function should just give me back the same structure I started with... Yet given the type of transpose, it definitely modifies the shape of the input structure. And at such a polymorphic type, with such a generic implementation, there's only so much it can be doing! How does it work!?

Before trying to solve that question, I wonder whether I could implement the identity function as a matrix traversal... Again, being type-directed:

\begin{spec}
matrixId : forall {m n X} → Vec (Vec X m) n → Vec (Vec X m) n
matrixId = traverse {!!}
\end{spec}

Can you guess the type of the hole? :-)

\begin{spec}
Goal: Vec .X .m → Vec .X .m
\end{spec}

And indeed, here comes the implementation:

\begin{spec}
matrixId : forall {m n X} → Vec (Vec X m) n → Vec (Vec X m) n
matrixId = traverse id
\end{spec}

Sounds familiar? Indeed, to implement matrix transposition and matrix identity, I wrote the exact same code! So something must be happening under the covers, at the level of implicit arguments.

Let's play the part of the unification algorithm with our two toy functions. Recall the full polymorphic type of traverse:

\begin{spec}
traverse : forall {F : Set → Set}{G S T}{{AG : Applicative G}} →
                  (S → G T) → F S → G (F T)
\end{spec}

So, by unification (the question-marked variables are now unification variables in scope):

\begin{spec}
-- by applying to id, ?S is unified with ?G ?T, therefore substituted
traverse id : (?G ?T → ?G ?T) → ?F (?G ?T) → ?G (?F ?T)
\end{spec}

For our two examples, we ascribe the following type signatures:

\begin{spec}
-- transpose
traverse id : Vec (Vec X m) n → Vec (Vec X n) m

-- matrixId
traverse id : Vec (Vec X m) n → Vec (Vec X m) n
\end{spec}

The following unification problems are to be solved:

\begin{spec}
-- transpose
?F ?S → ?G (?F ?T) ~= Vec (Vec X m) n → Vec (Vec X n) m

-- matrixId
?F ?S → ?G (?F ?T) ~= Vec (Vec X m) n → Vec (Vec X m) n
\end{spec}

This gives rise to the following unification equations:

\begin{spec}
-- transpose
?F (?G ?T) ~= Vec (Vec X m) n
?G (?F ?T) ~= Vec (Vec X n) m

-- matrixId
?F (?G ?T) ~= Vec (Vec X n) m
?G (?F ?T) ~= Vec (Vec X n) m
\end{spec}

And here are the potential solutions:

\begin{spec}
-- transpose
1: ?T = X ; ?F = fun S → Vec S n ; ?G = fun S → Vec S m

-- matrixId
1: ?T = X ; ?F = fun S → Vec (Vec S n) m ; ?G = id

2: ?T = X ; ?F = id ; ?G = fun S → Vec (Vec S n) m
\end{spec}

However, another additional constraint, namely the implicit instance argument that requires $?G$ to be an applicative functor, prevents the second equation from being solved, as we did not provide a way for Agda to build nested instances.

The mystery is therefore solved: even though we wrote the same code, the implicit arguments have been inferred, type-directed by the unification, to be different. In the case of matrix transposition, the F-structure is the outermost vector layer, and the G-effect is the innermost vector layer. In the case of matrix identity, the entire matrix is the F-structure, and the G-effect is identity. It makes sense then, that traversing with no effect and the identity function preserves the matrix completely.

One may now wonder how come traversing a vector with a vector effect effectively transposes the entire structure, seen as a matrix. It is actually fairly simple once you start unfolding the definitions:

\begin{spec}
-- note that (1 , 2) stands for (1 , 2 , $\diamond$), for simplicity and brevity
  traverse id ((1 , 2) , (3 , 4) , (5 , 6))
-- unfolding traverse for F = $\lambda$ S $\rightarrow$ Vec S 3, that is unfolding traverseVec
= pure _,_ <*> id (1 , 2) <*> vtr id ((3 , 4) , (5 , 6))
-- repeatedly unfolding recursive calls to vtr
= pure _,_ <*> id (1 , 2) <*>
  (pure _,_ <*> id (3 , 4) <*>
  (pure _,_ <*> id (5 , 6) <*> pure <>))
-- unfolding id...
= pure _,_ <*> (1 , 2) <*> (
  pure _,_ <*> (3 , 4) <*> (
  pure _,_ <*> (5 , 6) <*> pure <>
  ))
-- unfolding pure, with the applicative instance for G = $\lambda$ S $\rightarrow$ Vec S 2
= ((_,_) , (_,_)) <*> (1 , 2) <*> (((_,_) , (_,_)) <*> (3 , 4)
  <*> (((_,_) , (_,_)) <*> (5 , 6) <*> (<> , <>)))
-- the applicative application performs position-wise function application
= ((1 , _) , (2 , _)) <*> (((3 , _) , (4 , _)) <*> (((5 , _) , (6 , _)) <*> (<> , <>)))
= (1,_ , 2,_) <*> ((3 ,_ , 4 ,_) <*> ((5) , (6)))
= (1,_ , 2,_) <*> ((3 , 5) , (4 , 6))
= ((1 , 3 , 5) , (2 , 4 , 6))
\end{spec}

All in all, matrix transposition is not implemented as a matrix traversal, but as a vector traversal with a column-building effect!

Finally, here is how it goes for matrix identity:

\begin{spec}
  traverse id ((1 , 2) , (3 , 4) , (5 , 6))
-- unfolding traverse for F = $\lambda$ S $\rightarrow$ Vec (Vec S 2) 3, that is unfolding traverseVec
= pure _,_ <*> id (1 , 2) <*> vtr id ((3 , 4) , (5 , 6))
-- repeatedly unfolding recursive calls to vtr
= pure _,_ <*> id (1 , 2) <*>
  (pure _,_ <*> id (3 , 4) <*>
  (pure _,_ <*> id (5 , 6) <*> pure <>))
-- unfolding id...
= pure _,_ <*> (1 , 2) <*> (
  pure _,_ <*> (3 , 4) <*> (
  pure _,_ <*> (5 , 6) <*> pure <>
  ))
-- unfolding pure, with the applicative instance for G = id
= _,_ <*> (1 , 2) <*> (_,_ <*> (3 , 4) <*> (_,_ <*> (5 , 6) <*> <>))
-- the applicative application performs just function application
= (1 , 2),_ <*> ((3 , 4),_ <*> (5 , 6))
= (1 , 2),_ <*> ((3 , 4) , (5 , 6))
= (1 , 2) , (3 , 4) , (5 , 6)
\end{spec}

\end{document}
