---
title: "Nelson-Oppen Combination in Maude"
author: Nishant Rodrigues
advisor: Dr. Jose Mesegeur
year: 2018
department: Mathematics
schools: University of Illinois at Urbana-Champaign
---

\newcommand \Z        {\mathbb Z}
\newcommand \intersect  {\cap }
\newcommand \union      {\cup }
\newcommand \rewrite  {\longrightarrow_R}
\newcommand \rewrites {\longrightarrow_R}
\newcommand \proves   {{\vdash}}
\newcommand \FO       {\text{FirstOrderFormula}}
\newcommand \model    {\text{mod}}

\newcommand \terms    {T_{\Sigma}}
\newcommand \vars     {\text{vars}}
\newcommand \F        {\mathcal F}
\newcommand \QF       {\text{QF}}
\newcommand \Lit      {\text{Lit}}
\newcommand \and      {\wedge}
\renewcommand \And    {\bigwedge}

\newcommand \sig             {\text{sig}}
\newcommand \fun             {\text{fun}}
\newcommand \pred            {\text{pred}}

\newcommand \SharedSorts     {S_0}
\newcommand \SharedVariables {X^{1, 2}}
\newcommand \onetwo {\{1, 2\}}
\newcommand \Equiv {\text{Equiv}}

% Replace phi with varphi. I find phi too similar to emptyset
\renewcommand \phi {\varphi}

\tableofcontents

<!-- 

> If the reason is "Maude provides good high-level language for writing down mathematical
> algorithms", then perhaps interleaving code snippets with the math makes sense (to show how they
> are structurally similar). If you can't massage the math to the point where it looks like the
> Maude, then maybe it's not as strong of a point.
>
> But yeah, that's the biggest thing, is motivating the whole thing. The intro is a good place for
> that. I would start by moving the SMT stuff into background, and starting the Intro from scratch.
> Make an outline of how the whole project progressed.
>
> 1.  We want more expressive theories in Maude. Algebra (equational fragment of FOL) is already
>     pretty damn good, but sometimes we want more of FOL.
> 2.  How can we make it so that fast algebraic decision procedures (unification, FVP), play nicely
>     with the non-algebraic stuff from the rest of FOL? Answer is Nelson Oppen.
> 3.  How can we harness all this power in Maude? Fortunately rewriting is reflective, so we can
>     implement NO directly in Maude as a prototype, and go from there.
>
> Maybe even insert some contexts about automated modelling/verification for the math folks as point
> (0). Stuff like, "Rewriting logic is a formalism for building rigorous rich models of systems and
> doing automated model checking. This approach has successfully been applied to prove many
> properties of things ranging from biological systems (cite Pathway Logic) to network protocols
> (cite Maude NPA/Fan's work) to concensus algorithms (cite Nobi's work), to programming languages
> (cite early K papers). The model produces are Kripke structures over states which are terms in an
> order-sorted algebra."

-->

1.  Introduction
    -   Maude is a language used for formal verification of models of systems.
        -   Rewriting theories have Kripke structures as their models
        -   and allow reasoning via LTL, CTL Model checkers and Reachability logic .
        -   Low representational distance between the logic and execution semantics
        -   Has been used for verification of lots of systems
            -   Biological systems
            -   Network Protocols (Maude NPA / Fan's)
            -   Concensus algorithms (Nobi)
            -   Programming Languages (K papers)
        -   We can use automated theorem provers, and model checkers
        -   Some of these proof systems are constrained by the power and expressiveness of that SMT
            solvers have.
    -   So you need SMT. But what is this Nelson-Oppen thing?
        -   In Maude, we can decide SAT for vars-sat, CVC4, ... . Since `var-sat` and other solvers
            in maude are not integrated. we cannot solve queries in that need the solver to span
            across multiple theories.
            -   `var-sat` handles Algebraic stuff,
            -   CVC4 handles other FOL theories,
            -   Congruence closure
        -   Nelson Oppen lets us integrate them (among others) in a thoery generic manner.
        -   Rewriting logic and hence maude is reflective, so we can write Nelson Oppen in Rewriting
            logic itself
2.  Background
    -   What is SMT?
        -   definition
        -   Prior to nelson-oppen what was the state
            -   Domain specific are efficient, but not flexible
            -   Generic are flexible but not efficient
    -   Logical foundations of Maude
        -   Made up of two logics, one contained in the other (pg. 10 MM)
        -   Equational Logic
            -   Quantifier free first-order logic
            -   many- / order-sorted logics
        -   What is Rewriting Logic
            -   Models are Kripke structures
        -   Reflection & Meta Level
            -   Formal Tools are actually written in the Meta Level
                -   CRC, termination tool, real time tool ...
                -   Rules can be non-determintistic, tools to explore state space, strategies
        -   Decision Procedures we have
            -   Variant Satisfiability
            -   Congruence Closures
            -   CVC4
3.  Nelson Oppen as a rewrite theory
    -   Conditions
        -   Stably Infinite
            -   Required by General Nelson Oppen
            -   Intuitively, it means that if a formula is satisfiable and we have a witness we can
                either produce an infinite number of witness or an infinite number of
                counter-examples, allowing us to satisfy any disequality in addition to that formula
        -   Optimally intersectable
    -   Working
        -   Purification
        -   Arrangements
        -   Sketch of algorithm
            -   Given any formula, we can convert it to DNF, Purify , converting it to a conj of
                literals in one of the two formulae
            -   If each set of pure conjunctions are satisfiable, there is some arrangement of
                shared variables that is satisfiable then by optimal intersectability the entire
                fomula is satisfiable.
            -   For a large number of variables this is difficult, so we iteratively try more and
                more equalities until we can add no more.
                -   In case the theory is convex, we are done
                -   Otherwise, if PHI $\implies$ DISJ, then we check each possible equality
4.  Nelson oppen as rewrite theory (fits inside this above?)
5.  Examples
    -   Walk through Convex List + Int example in detail
    -   Real Hereditarily Finite sets
6.  Future direction
    -   Expand to more than two theories
    -   Optimize
    -   Take advantage of constructor variants
    -   Integrate with SAT solver

\pagebreak

Introduction
===========

Background
==========

Satisfiability modulo theories (SMT)
------------------------------------

Given a first-order logic formula $\phi$ with variables in the signature
of a theory $T$, a common problem is to find an assignment that
satisfies that formula. The decision problem for whether there is such a
satisfying assignment is called SMT. In the case of the theory of linear
arithmetic, this problem is called linear programming, and the Simplex
algorithm can be used to solve SMT problems.

Several algorithms have been devised for efficiently solving SMT
problems for different theories such as the theory of .... as well as
general methods for free algebras modulo axioms such as associativity with
commutativity etc. However, when working with formulae spanning multiple
such theories, these algorithms do not compose trivially, and additional
work must be done to prove that the procedure for solving these combined
formula are sound.

The Nelson-Oppen Combination method is a general method for combining
procedures that work on these subtheories for fairly general subtheories for
quantifier free formulae.

Equational Logic
----------------

A *signature* $\Sigma$ is a set of function symbols and their arities.
An *equational theory* is a pair $(\Sigma, E)$, where $E$ is a set of
algebraic identities on the terms $\terms$ constructed from the
signature $\Sigma$. For example, the group $\Z_5$ could be described as
an equational theory as follows: $$\Sigma = \{ 0, 1, \_+\_, -\_ \}$$

Note that underscores in the signature indicate holes for subterms, and
thus the arity of the symbol.

$$
\begin{aligned}
x + (y + z)               &= (x + y) + z &\quad\quad& \text{Associativity}       \\
x + y                     &= y + x       &\quad\quad& \text{Commutativity}       \\
x + (-x)                  &= 0           &\quad\quad& \text{Inverses}            \\
-(x + y)                  &= (-x) + (-y) &\quad\quad& \text{Inverse distributes} \\
(1 + (1 + (1 + (1 + 1)))) &= 0           &\quad\quad& \text{Modulo 5}            \\
\end{aligned}$$

The expressiveness of Equational logic can be tuned by allowing
signatures to carry more or less information. In *many-sorted*
equational logic, each function symbol is also attached to a list of
argument sorts $s_1, s_2, \ldots, s_n$, and a _result sort_.
Thus, in a many sorted equational theory, the signature is the $(S, \Sigma)$ 
where $S$ is a set of sorts, and $\Sigma$ is a set of function symbols with
argument and result sorts in $S$. For example, a vector space would have
sorts `Vector` and `Scalar`.

Furthur, by adding a partial order $<$ on the sort symbols, we get the more
expressive order-sorted equational logic. If $s_i < s_j$ we say that $s_i$ is
a subsort of $s_j$. For example, we could have `Integer < Rational < Real`.

Rewriting Logic
---------------

A rewrite theory $\mathcal R$ is the triple $(\Sigma, E, R)$, where
$(\Sigma, E)$ is an equational theory and $R$ the set of *one step
rewrites* on the terms of the signature.
The rewrite rules describe a relation $\rewrite \subset \terms\times \terms$.
The sentences that $\mathcal R$ proves is obtained from the finite application of the following
rules:

-   **Reflexitivity:** For each term $t \in \terms(X)$,
    $$\infer{t \rewrites t} {}$$
-   **Equality:**
    $$\infer{ u' \rewrites v'}{ u \rewrites v & E \proves u = u' & E \proves v = v'}$$
-   **Congruence:** For each $f : k_1 \cdots k_n \to k$ in $\Sigma$, and
    $t_i, t_i' \in \terms(X), 1 \le i \le n$,
    $$\infer{f(t_1,\ldots, t_n) \rewrites f(t'_1, \ldots, t'_n)}{t_1 \rewrites t'_1 & \cdots & t_n \rewrites t'_n}$$
-   **Replacement:** For each rule $r : t \rewrites t'$ in $R$, with
    $\vars(t) \union \vars(t') = \{x_1, \ldots x_n\}$, and for each
    substitution,
    $\theta : \{x_1, \ldots x_n\} \longrightarrow \terms(X)$ with
    $\theta(x_1) = p_l$ with $\theta(x_l) = p_l, 1 \le l \le n$, then:
    $$\infer{\theta(t) \rewrites \theta'(t')}
            { p_1 \rewrites p'_1 & \cdots & p_n \rewrites p'_n}$$
-   **Transitivity:**
    $$\infer{ t_1 \rewrites t_3 } {t_1 \rewrites t_2 & t_2 \rewrites t_3 }$$

If $x \rewrites y$, we say "$x$ rewrites to $y$". 

[20 years of rewriting]

Maude
-----

The programing language, Maude, is based on rewriting logic.
A program in Maude is a rewrite theory, and a computation is a deduction based
on the inference rules above.

An equational theory is specified as a _functional modules_:

```
fmod Z5 is
    sorts NzZ5 Z5 .
    subsorts NzZ5 < Z5 .

    op 0 : -> Z5                        [ctor] .
    op 1 : -> NzZ5                      [ctor] .
     
    op _ + _ : Z5 Z5 -> Z5   [assoc comm id: 0] .
    op   - _ : Z5    -> Z5 .

    vars x y : Z5 .

    eq -(x) + -(x) = 0 .
    eq -(x  + y)   = -(z) + -(y) .
endfm
```

This program represents an equational theory
$E = ((S, \le_S), \Sigma, E \union B)$. Here, $S = \{$`NzZ5`$,$
`Z5`$\}$, $\le_s = \{ ($ `NzZ5`$,$ `Z5` $\}$ and
$\Sigma = \{ 0, 1, \_ + \_ , - \_ \}$.
Although ordinarily equations in equational theories are symetric -- in a proof
we may replace equals with equals if  a term matches either the left hand side
or the right hand side -- equations in maude only apply from left to right.

This is to allow terminating execution. Some equations may also be
specified implicitly as atrributes as associativity (`assoc`),
commutativity (`comm`) and identity (`id: 0`) are specified above.
Besides being convenient, it also allows specification of equations that would
otherwise make execution non-terminating and make execution more efficient.

This set of attributes $E$, along with equations $B$ specified with the
`eq` keyword together make up the equations $E \union B$ that are used
to define an equational theory.

For the theory to be well defined, we require that these equations be:

* Confluent
* functions should respect sorts (preregular??)

[XXX expand]

Defining a program as above means that there is an extremely small
representational distance between the programs and the mathematical
logic we use to reason about them.

### Maude Meta Level

Rewriting logic is a *reflective logic* -- its meta theory can be
represented at the object level in a consistant way. i.e. there is a
function $\overline { ( \_ \proves \_ ) }$ such that for any theory $T$,
$T \proves \phi \iff U \proves \overline{ T \proves \phi }$.

The module `META-LEVEL` is used to do this lifting. `META-LEVEL`'s
`upModule` function allows us to lift a theory and perform rewrites with
it like any other term.

[Reflection in General Logics, Rewriting Logic and Maude]:
https://www.sciencedirect.com/science/article/pii/S1571066105825538

### Decision Procedures in Maude

Some satisfiability procedures have been been implemented in Maude. We
will use these solvers as the subsolvers for Nelson-Oppen.

#### Variant Satisfiability

Variant satisisfiability is an algorithm to decide quantifier free
satisfiability of an initial algebra $T_{\Sigma/E}$ when the equational
theory $(\Sigma, E)$ has the finite variant property and its constructors
satitisfy a compactness condition.

Decomposition of equational theory
:  XXX

Variant
:   Given a decomposition $\mathcal R = (\Sigma, E, R)$ of an OS equational theory
    $(\Sigma, E)$ and a $\Sigma-$term t, a variant of $t$ is a pair $(u, \theta)$
    such that:
    
    1. $u =_B (t\theta)!_{R,B}$
    2. If $s \notin \vars(t)$ then $x\theta = x$, and
    3. $\theta = \theta!_{R,B}$, that is, $x\theta = (x\theta)!_{R,B}$ for all
       variables $x$.
       
Most General Variant
:   Given variants $(u, \theta)$ and $(v, \gamma)$ of $t$, $(u, \theta)$ is
    more general than $(v, \gamma)$ iff there is a substitution $\rho$ such
    that:
    
    1. $\theta_\rho =+B \gamma$ and
    2. $u\rho =_b v$
    
Finite Variant Property
:   The decomposition $\mathcal R = (\Sigma, B, R)$ of $(\Sigma, E)$ has the
    finite variant property iff for each $\Sigma-$term $t$ there is a finite
    most general complete set of variants.

* Note on var-sat and countably infinite sorts

#### CVC4

Order Sorted Nelson Oppen as a rewrite theory
=============================================

Given decision procedures for the satisfiablilty of two theories,
meeting certain conditions,  the Nelson-Oppen Combination algorithm
derives an algorithm for the satisfiablilty of the union of these theories.

In [OS Nelson-Oppen] Dr Tinelli generalizes this process to Order-Sorted theories.

Conditions on the theories
--------------------------

For the Nelson Oppen method to be viable, the theories must meet some basic conditions.

Stably Infinite

: Let $T$ be an order-sorted first-order theory with signature
$\Sigma = ((S, \le), F, P)$ and $s_1, s_2,\ldots s_n \in S$. Let
$\F \subset \FO(\Sigma)$, be the set of first order formulae in $\Sigma$

    $T$ is stably infinite in sorts $s_1, s_2,\ldots s_n$ for
    $\F-$satisfiability iff every $T-$satisfiable formula
    $\phi \in \F$, is also satisfiable in a model
    $\mathcal B = (B, \__B) \in \model(T)$ such that
    $|B_{s_i}| \ge \chi_0, 1 \le i \le n$.

    Intuitively, a theory is stably finite if for each sort $s_i$,
    if for each satisfiable formule with witness $x$ of sort $s_i$, there is another
    distinct witness $y$.


Notation: For sort $s$ and signature $\Sigma_i$, let $[s]_i$ denote it's
connected component of sorts in $\Sigma_i$

Optimally intersectable

:   The order-sorted signatures $\Sigma_1$ and $\Sigma_2$ are optimally
    intersectable iff:

    1.  **Functions and predicates sorts agree:** For each
        $f \in \fun(\Sigma_1) \intersect \fun(\Sigma_2)$ (resp,
        $p \in \pred(\Sigma_1) \intersect \pred(\Sigma_2)$),
        $\exists \{i, j\} \in \onetwo$ such that:

        -   $F_i(f) = F_j(f) \intersect ([s_1]_i\times\cdots\times [s_m]_i) \times [s_i]$
            (resp
            $P_i(p) = P_j(p) \intersect ([s_1]_i\times\cdots\times [s_m]_i)$

        -   $[s_l] \subset [s_l]_j, 1 \le l \le n$, and
            $[s]_i \subset [s]_j$ (resp.
            $[s_l]_i \subset [s_l]_j, 1 \le l \le n$).

    2.  **Intersection is a single component:** For every sort
        $s \in \SharedSorts$, we have
        $[s]_1 \intersect S_2 = [s]_2 \intersect [s]_1 = [s]_1\intersect [s]_2$

    3.  and, for any two sorts $s_i \in S_i$ and $s_j \in S_j$ any one
        of:

        i.  **Intersection is empty**:
            $[s_i]_i \intersect [s_j]_j = \emptyset$

        ii. **Intersection is the top sort of one component:**
            $[s_i]_1 \intersect [s_j]_2 = \{s_0\}$, where $s_0$ is the
            top-sort of atleast one of the connected components.

        iii. **Once component is subsumed in the other:**

             a.  $\exists k \in \onetwo$ and $[s_k]_k$ has a top sort,
                 $[s_k]_k \subset [s_l]_l$ $\{k, l\} = \onetwo$.
             b.  $\le_k \intersect [s_k] = \le_l \intersect [s_k]_2^2$
             c.  (downward closure):
                 $\forall s \in [s_l]_l, \forall s' \in [s_k]_k, s\le_l s' \implies s\in [s_k]_k$

$$\begin{aligned}
\text{TODO: Diagrams of allowed component intersections}
\\ \\ \\ \\ \\ \\ \\
\end{aligned}$$

<!--

Optimally Intersectable

:   The order sorted signatures are *optimally intersectable*, denoting
    as $[s_i]_i$ as the connected component $(S_i, \le_i)$ of a sort
    $s_i \in S_i, i \in \onetwo$. either:

    either:
    
    1.  $[s_i]_i \intersect [s_j]_j \ne \emptyset$,
        $\{ i, j \} \subset \onetwo$ and for $k \in \{1, 2\}$, we have:

        a.  $\exists k \in \onetwo$ and $[s_k]_k$ has a top sort,
            $[s_k]_k \subset [s_l]_l$ $\{k, l\} = \onetwo$.
        b.  $\le_k \intersect [s_k] = \le_l \intersect [s_k]_2^2$
        c.  (downward closure):
            $\forall s \in [s_l]_l, \forall s' \in [s_k]_k, s\le_l s' \implies s\in [s_k]_k$
        d.  (uniqueness):
            $[s_i]_i \intersect S_j = [s_j]_j \intersect S_i = [s_k]_k$

    2.  $[s_i]_i \intersect [s_j]_j = \{ s_0 \}, \{i, j\} = \onetwo$,
        and $\exists k \in \onetwo$ such that $s_0$ is the top element
        of $[s_k]_k$

        (uniqueness):
        $[s_i]_i \intersect S_j = [s_j]_j \intersect S_i = [s_k]_k$

    and:

    -   If $f \in \fun(\Sigma_1) \intersect \fun(\Sigma_2)$
        (resp, $p \in \pred(\Sigma_1) \intersect \pred(\Sigma_2)$
        then $\exists \{i, j\} \in \onetwo$ such that:

        if $(s_1,\ldots, s_n, s) \in F_i(f)$
        (resp. $(s_1, \ldots, s_n) \in P_i(p)$
        then:

        * | $F_i(f) = F_j(f) \intersect ([s_1]_i\times\cdots\times [s_m]_i) \times [s_i]$
          | (resp $P_i(p) = P_j(p) \intersect ([s_1]_i\times\cdots\times [s_m]_i)$

        * | $[s_l] \subset [s_l]_j, 1 \le l \le n$, and $[s]_i \subset [s]_j$
          | (resp. $[s_l]_i \subset [s_l]_j, 1 \le l \le n$).
-->          

Purification
------------

Given a formula $\phi = \And \Lit(\Sigma_1 \union \Sigma_2)$ , purification
is a transformation that gives us a formaule $\And \Lit(\Sigma_1) \and \And\Lit(\Sigma_2)$
that is equivalent for satisfiability.

Inference rules for Order-Sorted Nelson-Oppen
---------------------------------------------

Given two order-sorted first-order theories, $T_1, T_2$, with signatures
$\Sigma_1, \Sigma_2$ optimally intersectable in the set of
sorts $S_0$, and $T_i$ satisfiability of quantifier free $\Sigma_i$ formulae
decidable, we want a decision procedure for $T_1 \union T_2$-satisfiability
of quantifier free $\Sigma_1 \union \Sigma_2$ formulae.

Since, we can convert any formula to disjunctive normal form, and purify
$\Sigma_1 \union \Sigma_2$-formulae so that the are the conjunction of
literals in each signature, we only need a decision procedure for $T_1 \union T_2$-satisfiability
refor $\And \Lit(\Sigma_1) \and \And \Lit(\Sigma_2)$ formulae.

Convex vs non-convex
--------------------


Inference System
----------------

Order Sorted Nelson-Oppen in Maude's `META-LEVEL`
===============================================

``` {include="maude/contrib/tools/meta.md/nelson-oppen-combination.md"}
```

Examples
========

* List + Rat example
* Hereditarily finite sets + Rats

https://ac.els-cdn.com/S0167642317301788/1-s2.0-S0167642317301788-main.pdf?_tid=9fa3ca91-7528-400b-ab94-8a2efd43b4fc&acdnat=1523049049_18ce07f410687584e04ea942f15cafb7
7.5 21

Conclusion & Future work
========================

-   Keeping track of variant ctors
-   Integrating with SAT solver - Boolean struture

