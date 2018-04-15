---
title: "Nelson-Oppen Combination in Maude"
author: Nishant Rodrigues
advisor: Dr. Jose Mesegeur
year: 2018
department: Mathematics
schools: University of Illinois at Urbana-Champaign
---

\newcommand \Z        {\mathbb Z}
\newcommand \rewrite  {\longrightarrow_R}
\newcommand \rewrites {\longrightarrow_R}
\newcommand \terms    {T_{\Sigma}}
\newcommand \rules    {\mathcal R}
\newcommand \proves   {\vdash}
\newcommand \FO       {\text{FirstOrderFormula}}
\newcommand \F        {\mathcal F}
\newcommand \model    {\text{mod}}
\newcommand \QF       {\text{QF}}
\newcommand \Lit      {\text{Lit}}
\newcommand \and      {\wedge}

\newcommand \intersect  {\cap }
\newcommand \union      {\cup }
\newcommand \sig             {\text{sig}}
\newcommand \SharedSorts     {S_0}
\newcommand \SharedVariables {X^{1, 2}}

# Introduction

## What is SMT? Why do we need SMT?

SMT solvers attempt to decide the satisfiability of first order formulae
that may include functions and predicate symbols from various theories,
such as Presburger Arithmetic, Reals, or lists.

History of solvers:

* Solvers: Theory specific, generalization, composition.
* The Nelson-Oppen Combination procedure
* Nelson Oppen in ordered sorted logics

# Preliminaries: Rewriting Logic & Maude

## Unsorted Rewriting Logic

A _signature_ $\Sigma$ consists of a set of function symbols and their arities.
An _equational theory_ is a pair $(\Sigma, E)$, where $E$ is a set of
algebraic identities on the terms $\terms$ constructed from the
signature $\Sigma$.
For example, the group $\Z_5$ could be described as an equational
theory as follows:
$$\Sigma = \{ 0, 1, \_+\_, -\_ \}$$

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

A rewrite theory $\rules = (\Sigma, E, R)$ is an equational theory
$(\Sigma, E)$ where $R$ is a set of rewrite rules. The rewrite rules
describe a relation $\rewrite \subset \terms\times \terms$. If
$x \rewrites y$, we say "$x$ rewrites to $y$".

The programming language, Maude, is based on rewriting logic.
The set of equivalence classes of terms modulo equality via $E$, $\terms/E$,
represent the state of a program, and the rewrite rules $\rules$ represent
transitions between the different states.

### Many-Sorted and Order-Sorted Rewriting Logic

The signature $\Sigma$ is an unsorted signature -- each function symbol
only has an arity assigned to it. A many-sorted signature
$\Sigma = (S, F)$ has a set $S$ of sorts, and $F$ is a set of function
symbols each associated with a list of sorts $s_1, s_2, \ldots, s_n$ called
the _argument sorts_ and a sort $s$ called the _result sort_.

Maude represents equational theories as `fmod`s or "functional modules".

Refs:

-   20 years of rewriting
-   476 notes

## Maude

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

[Expand]

### Maude Meta Level

Rewriting logic is a *reflective logic* -- its meta theory can be
represented at the object level in a consistant way. i.e. there is a
function $\overline { ( \_ \proves \_ ) }$ such that for any theory $T$,
$T \proves \phi \iff U \proves \overline{ T \proves \phi }$.

[Reflection in General Logics, Rewriting Logic and Maude]:
https://www.sciencedirect.com/science/article/pii/S1571066105825538

Maude's `META-LEVEL` allows lifting theories and terms to the meta level
and ...

## Decision Procedures in Maude

### CVC4

Maude has a interface to the CVC4 SMT solver, ...

### Variant Satisfiability

* Note on var-sat and countably infinite sorts

# Order Sorted Nelson Oppen as a rewrite theory (CS576 notes)

Given decision procedures for the satisfiablilty of two theories,
meeting certain conditions,  the Nelson-Oppen Combination algorithm
derives an algorithm for the satisfiablilty of the union of these theories.

In [OS Nelson-Oppen] Dr Tinelli generalizes this process to Order-Sorted theories.

## Conditions on the theories.

Stably Infinite

:   Let $T$ be an order-sorted first-order theory with
    $\sig(T) = \Sigma ((S, \le), F, P) ; s_1, s_2,\ldots s_n \in S$ and
    $\F \subset \FO(\Sigma)$, a recursive set.

    T is called stably infinite in sorts $s_1, s_2,\ldots s_n$ for
    $\mathcal F-$satisfiability iff every $T-$satisfiable formula
    $\phi \in \F$ $\phi$ is also satisfiable in a model
    $\mathcal B = (B, _B) \in \model(T)$ such that
    $|B_{s_i}| \ge \chi_0, 1 \le i \le n$.

Optimally Intersectable

:    ...

## Inference rules for Order-Sorted Nelson-Oppen

Given: $T_1, T_2$, OS-FO theories, with $\Sigma_i = \sig(T_i), i \le i \le 2$ with $\Sigma_1, \Sigma_2$
optimally intersectable in many-sorted set of sorts $(S_0, =_{s_0})$, with $S_0 = \{ s_1, \ldots, s_n\}$
with $T_i-$ satisfiability of quantifier free $\Sigma_i$ formulae decidable, $1 \le \le 2$.

We want: A decision procedure for $T_1 \union T_2$ -satisfiability
of quantifier-free $(\Sigma_1 \union \Sigma_2)$ formulae.

It is enough to have a decision procedure for formulae that are conjunctions
of atoms in either signature

Because of the formula transformations:

$$                   (T_1 \union T_2, \QF(\Sigma_1 \union \Sigma_2))
\iff{DNF}           (T_1 \union T_2, \And \Lit(T_1 \union T_2))
\iff {purification} (T_1 \union T_2, \And \Lit(T_1) \and \And \Lit(T_2))
$$.


## Convex vs non-convex

## Inference System

# Order Sorted Nelson-Oppen in Maude's META-LEVEL

# Examples

* Hereditarily finite sets + Rats
* Integrating with ctor variants from var-sat

https://ac.els-cdn.com/S0167642317301788/1-s2.0-S0167642317301788-main.pdf?_tid=9fa3ca91-7528-400b-ab94-8a2efd43b4fc&acdnat=1523049049_18ce07f410687584e04ea942f15cafb7
7.5 21

# Conclusion & Future work

* Keeping track of variant ctors
* Integrating with SAT solver - Boolean struture
