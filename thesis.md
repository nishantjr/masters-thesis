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
\newcommand \proves   {\vdash}
\newcommand \FO       {\text{FirstOrderFormula}}
\newcommand \model    {\text{mod}}

\newcommand \terms    {T_{\Sigma}}
\newcommand \F        {\mathcal F}
\newcommand \QF       {\text{QF}}
\newcommand \Lit      {\text{Lit}}
\renewcommand \and      {\wedge}
\renewcommand \And    {\bigwedge}

\newcommand \sig             {\text{sig}}
\newcommand \fun             {\text{fun}}
\newcommand \pred            {\text{pred}}

\newcommand \SharedSorts     {S_0}
\newcommand \SharedVariables {X^{1, 2}}
\newcommand \onetwo {\{1, 2\}}
\newcommand \Equiv {\text{Equiv}}

\tableofcontents

1. Introduction (2-3 pages)
2. Preliminaries (3-4 pages)
   - Rewriting
   - Maude
   - MetaLevel
3. Order Sorted Nelson Oppen as a Rewrite theory  (5-6 pages)
4. OS NO in Maude's Meta LEvel (5-6 pages)
5. Examples (5) (7-pages)
6. Conclusion 2 pages

\pagebreak

Introduction
============

Satisfiability modulo theories (SMT)
------------------------------------

Given a first-order logic formula $\phi$ in the signature of a theory
$T$ , SMT is the decision problem of deciding whether this formula is
satisfiable. For example, the Simplex algorithm is a well-known SMT
solver for linear arithmetic.

The Nelson Oppen combination method is a fairly general methods for combining
decision procedures for theories $T_1$ and $T_2$ into a decision procedure
for the theory $T_1 \union T_2$.


Preliminaries: Rewriting Logic & Maude
======================================

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
Thus in a many sorted equational theory, the signature is the $(S, \Sigma)$ 
where $S$ is a set of sorts, and $\Sigma$ is a set of function symbols with
argument and result sorts in $S$. For example, a vector space would have
sorts `Vector` and `Scalar`.

Furthur, by adding a partial order $<$ on the sort symbols, we ge the more
expressive order-sorted equational logic. If $s_i < s_j$ we say that $s_i$ is
a subsort of $s_j$. For example, we could have `Integer < Rational < Real` .

Rewriting Logic
---------------

A rewrite theory $\mathcal R$ is the triple $(\Sigma, E, R)$, where $(\Sigma, E)$ is an equational theory
and $R$ relation among the terms of that signature.
The rewrite rules describe a relation $\rewrite \subset \terms\times \terms$. If
$x \rewrites y$, we say "$x$ rewrites to $y$".

Depending on the expressiveness of the signature $\Sigma$, we may have
un-sorted, many-sorted and order-sorted rewriting logic theories.

Maude
-----

The programming language, Maude, is based on rewriting logic.
The set of equivalence classes of terms modulo equality via $E$, $\terms/E$,
represent the state of a program, and the rewrite rules $R$ represent
transitions between the different states.

The maude programming language represents programs as an aroder sorted rewrite theory over
a term. An equational theory is described with _functional modules_.

```
fmod Z5 is
    sorts Z5 .
    op 0 : -> Z5 [ctor] .
    op 1 : -> Z5 [ctor] .

    op _ + _ : Z5 Z5 -> Z5 [assoc comm id 0] .
    op   - _ : Z5    -> Z5 .

    vars x y : Z5 .

    eq -(x  + y)   = -(z) + -(y) .
    eq -(x) + -(x) = 0 .
endfm
```

Although equations in equations in equational theories are commutative
in the order of left and right hands, equations in maude have a prefered
direction - the term on the left rewrites to the term on the right.
Having a prefered direction and specifying equations like commutativity
as attributes allow us to use equations as an operational sementics.
i.e. use the equations to drive a terminating execution.

This mean, we need:

* Confluence
* functions should respect sorts (preregular??)
* terminating

Since the representational distance between maude programs and rewriting logic
is small, it becomes easy to reason about programs written in Maude.

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

:   Let $T$ be an order-sorted first-order theory with
    signature $\Sigma = ((S, \le), F, P)$ and $s_1, s_2,\ldots s_n \in S$. 
    Let $\F \subset \FO(\Sigma)$, be the set of first order formulae in $\Sigma$

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

Inference rules for Order-Sorted Nelson-Oppen
---------------------------------------------

Given: $T_1, T_2$, OS-FO theories, with $\Sigma_i = \sig(T_i), i \le i \le 2$ with $\Sigma_1, \Sigma_2$
optimally intersectable in many-sorted set of sorts $(S_0, =_{s_0})$, with $S_0 = \{ s_1, \ldots, s_n\}$
with $T_i-$ satisfiability of quantifier free $\Sigma_i$ formulae decidable, $1 \le \le 2$.

We want: A decision procedure for $T_1 \union T_2$ -satisfiability
of quantifier-free $(\Sigma_1 \union \Sigma_2)$ formulae.

It is enough to have a decision procedure for formulae that are conjunctions
of atoms in either signature

Because of the formula transformations:

$$                  (T_1 \union T_2, \QF(\Sigma_1 \union \Sigma_2))
\iff{DNF}           (T_1 \union T_2, \And \Lit(T_1 \union T_2))
\iff {purification} (T_1 \union T_2, \And \Lit(T_1) \and \And \Lit(T_2))
$$.

Convex vs non-convex
--------------------

Inference System
----------------

Order Sorted Nelson-Oppen in Maude's `META-LEVEL`
===============================================

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

