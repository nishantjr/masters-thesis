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
\renewcommand \lor     {\vee }
\newcommand \Or     {\bigvee}
\renewcommand \And    {\bigwedge}
\newcommand \limplies {\longrightarrow }

\newcommand \sig             {\text{sig}}
\newcommand \fun             {\text{fun}}
\newcommand \pred            {\text{pred}}

\newcommand \purified        {\text{xxxpurified}}
\newcommand \arrangements    {\text{xxxarrangements}}

\newcommand \SharedSorts     {S_0}
\newcommand \SharedVariables {X^{1, 2}}
\newcommand \onetwo {\{1, 2\}}
\newcommand \Equiv {\text{Equiv}}

\renewcommand \phi {\varphi}

\newcommand \NelsonOppenSat {\text{NelsonOppenSat}} 
\newcommand \CheckSat       {\text{CheckSat}} 
\newcommand \CandidateEqualities {\text{CE}} 

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

-   Maude is a language used for formal verification of models of systems.
    -   Has been used for verification of lots of systems
        -   Biological systems
        -   Network Protocols (Maude NPA / Fan's)
        -   Concensus algorithms (Nobi)
        -   Programming Languages (K papers)
    -   Programs are represented as Rewrite theories
        -   have Kripke structures as their models
        -   Low representational distance between the logic and execution semantics
        -   allow reasoning via LTL, CTL Model checkers and Reachability logic .
    -   We can use automated theorem provers, and model checkers
        -   Rewriting logic and hence maude is reflective, so we can write Nelson Oppen in Rewriting
            logic itself
    -   Some of these tools are constrained by the power of SMT available to them
-   Many Formal Verification tools (Model Checkers, deductive provers) rely on SMT to be effective.
    -   Several efficient algorithms exist for some well known theories such as Linear Arithemetic,
        real and complex arithmetic.
    -   There are also general algorithms for SMT over algebraic theories with axioms like
        associativity and commutativity.
    -   However, we often need to solve SMT problems that span accross multiple such theories.
    -   The Nelson Oppen combination method allows combining SMT solvers for theories that meet
        fairly unassuming criteria, into a solver for the quantifier free fragment of the union of
        these theories.
-   So you need SMT. But what is this Nelson-Oppen thing?
    -   When programming in Maude, there are several solvers available to us.
    -   Some like CVC4 are external tools
    -   Others are implemented in maude itself
    -   These are
        -   `var-sat` handles Algebraic stuff,
        -   CVC4 handles other FOL theories,
        -   Congruence closure
    -   Although CVC4 implements nelson-oppen internally, it cannot be combined with other solvers
        implemented in the maude `META-LEVEL`.
    -   Since `var-sat` and other solvers in maude are not integrated. We cannot solve queries in
        that need the solver to span across multiple theories.
    -   Nelson Oppen lets us integrate them (among others) in a theory generic manner.

-->

\pagebreak

Introduction
===========

The Maude programming language is based on rewriting logic. It is often used for modeling and
verification of systems. It has been used to verify a wide spectrum of systems, from biological
systems (Pathway Logic \cite{}), to Network Protocols (Maude NPA \cite{}), to concensus algorithms,
and programming languages (KFramework).

Maude derives its semantics from rewriting logic, and programs are represented as rewrite theories.
This means that there is a small representational distance between rewriting logic and execution of
programs in Maude.

Kripke structures, commonly used in Model Checkers to represent the behaviour of a system, are
models of rewrite theories. Further, Rewriting Logic, and hence Maude, is reflective allowing
implementing in Maude algorithms that manipulate rewrite theories. This makes it a particularly easy
target for model checkers using LTL, CTL etc, and even automated theorem provers like Reachability
Logic.

Many of these formal verification tools are constrained by the power of SMT solvers available to
them. Over the years, efficient solvers have been devised for linear integer arithmetic, real and
complex arithmetic, and also general algorithms for algebraic theories with axioms like
associativity and commutativity. There is, however, often a need for solvers for formulae that span
multiple theories. The Nelson Oppen combination method, published in 1979, allows combining SMT
solvers for theories that meet some fairly unassuming criteria into a solver for the quantifier free
fragment of the union of those theories.

Maude makes a few SMT solvers available programmers. Some like CVC4 are external tools integrated
into Maude via its C++ API. Others like `var-sat` and congruence closure are implemented in Maude
itself, using the `META-LEVEL` to take advantage of reflection. While CVC4 does implement the
Nelson-Oppen algorithm for combining the theories it provides, there is currently no way to combine
it with the solvers not part of CVC4, such as those implemented at the the `META-LEVEL`.
In this thesis, we implement the Nelson-Oppen Combination Method in Maude, and instantiate
with it CVC4 and `var-sat`.

Background
==========

Satisfiability Modulo Theories (SMT)
------------------------------------

Given a first-order logic formula $\phi$ with variables in the signature of a theory $T$, a common
problem is to find an assignment of variables for which the formula evaluate to true. The decision
problem for checking whether such a satisfying assignment exists is called Satisfiability Modulo
Theories (SMT). In the case of the theory of linear arithmetic, this problem is called linear
programming, and the Simplex algorithm is a well-known algorithm for solving linear programming SMT
problems.

Several algorithms have been devised for efficiently solving SMT problems for different theories, as
well as general methods for free algebras modulo axioms such as associativity with commutativity
etc.

However, when working with formulae spanning multiple such theories, these algorithms may not
compose trivially, and additional work must be done to prove that the procedure for solving these
combined formula are sound. Further, even if a general algorithm works for a specific theory, there
may be more efficient algorithms for solving that problem.

In 1979, Nelson and Oppen published the first general algorithm for deciding the satisfiability of
formulae in the union of two theories, provided they meet two conditions:

1.  The theories are "stably infinite"
2.  Their signatures are disjoint.

Later, in \cite{},  Tinelli generalized this algorithm and formalised it for order-sorted logic,
which Maude implements. 

Logical Foundations of Maude
============================

Maude is based on two logics, one contained in the other. 

The first, equational logic, is the quantifier free fragment of first-order logic with equality. The
second, rewriting logic, is defined by transitions between equivalence classes of terms defined by
an equational theory.

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

Further, by adding a partial order $<$ on the sort symbols, we get the more
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

<!--

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

-->

Models of rewrite theories are Kripke structure. Kripke structures are


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

-   Sets (non-recursive) of Ints, Reals, etc
-   Algebraic data types (axioms list `comm, assoc` not allowed)
-   Linear real , subset of non-linear that can be converted to linear.

Order Sorted Nelson Oppen as a rewrite theory
=============================================

<!--

3.  Nelson Oppen as a rewrite theory
    - Order sorted is nicer that many-sorted and unsorted, because we omit
      arrangements where there are equalities that are obviously unsatisfaible
      at the sort level.
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

-->

Conditions on the theories
--------------------------

For the Nelson Oppen method to be viable, the theories must meet some conditions.

2. They must be stably infinite
3. They must be optimally intersecting.

Stably Infinite

:   Let $T$ be an order-sorted first-order theory with signature $\Sigma = ((S, \le), F, P)$ and
    $s_1, s_2,\ldots s_n \in S$. Let $\F \subset \FO(\Sigma)$, be the set of first order formulae in
    $\Sigma$

    $T$ is stably infinite in sorts $s_1, s_2,\ldots s_n$ for $\F-$satisfiability iff every
    $T-$satisfiable formula $\phi \in \F$, is also satisfiable in a model
    $\mathcal B = (B, \__B) \in \model(T)$ such that $|B_{s_i}| \ge \chi_0, 1 \le i \le n$.

    Intuitively, it means that if a formula is satisfiable and we have a witness we can either
    produce an infinite number of witness or an infinite number of counter-examples, allowing us to
    satisfy any disequality in addition to that formula


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

        XXX requirement that no common function and predicate symbols removed?
        What guarantees that functions and predicates are the same when restricted
        to the intersection?

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

\begin{figure}
$$\begin{aligned}
\\ \\ \\ \\ \\ \\ \\
\end{aligned}$$
\caption{XXX: Diagrams of allowed component intersections}
\end{figure}


Overview
--------

Given two order-sorted, optimally intersecting, stably-infinite theories $T_1$ and $T_2$ with
signatures $\Sigma_1$ and $\Sigma_2$ each with decision procedures for quantifier free
$T_i$-satisfiability we want to derive a decision procedure for quantifier free $T_1 \union T_2$
satisfiability.

We can transform any formula $\phi$ into an *equi-satisfiable* formula in disjunctive normal form.
Furthur, for each atom in such a formula we can apply "purification" to obtain a formula with each
atom in the signature of one of the theories.

Now, our task has become to find a model $M_0$ and an assigment $a: \vars(\phi) \to M_0$ such that
$M_0, a \models \purified$. In general, this requires knowing thde semantics of each of the
theories, but in the case of stably infinite theories, the task is easier. With stably infiniteness,
since every satisfiable formula has an infinite model, if we need a value distinct from a witness we
have infinite choices for either the value or the witness. i.e.
$$T_1 \union T_2 \not\models \phi \land \vec t_k \ne \vec t'_k 
\iff T_i \models \phi \limplies \vec t_k = \vec t'_k$$
This means that we do not need to find a specific arrangement, but just a satisfiable equivalence
relation of the shared variables. For any formula, $\purified$, we have an equisatisfiable formula
$\arrangements$. Since for stably infinite theories we only care about the equivalence class being
satisfiable, we can project this formula onto each of the theories and check satisfiability.

\begin{figure}
$$\begin{matrix*}[l]
                    &    &                        &     & T_{\union}  \models& \QF(\Sigma_1 \union \sigma_2)                                              \\
\text{DNF}          &\iff&                        &     & T_{\union}  \models& \And \Lit(\Sigma_1 \union \sigma_2)                                        \\
\text{Purification} &\iff&                        &     & T_{\union}  \models& \And \Lit(\Sigma_1) \land \And\Lit(\sigma_2)                                \\
\text{Arrangement}  &\iff&                        &     & T_{\union}  \models& \Or ( \And \Lit(\Sigma_1) \land \And\Lit(\sigma_2) \land \And \phi_{\equiv} )\\
\text{Projection}   &\iff& \exists \phi_{\equiv}, &     & T_1 \models        & \And \Lit(\Sigma_1) \land \And \phi_{\equiv}                                \\
                    &    &                        &\text{and} & T_2 \models        & \And \Lit(\Sigma_2) \land \And \phi_{\equiv}
\end{matrix*}$$
\caption{Equisatisfiable formulae transformations on stably infinite theories we use for NO}
\end{figure}

Inference rules for Order-Sorted Nelson-Oppen
---------------------------------------------

Note that up to this point, we have only found a mathematically sound way of finding satisfiability
but do not yet have a viable efficient algorithm.
Checking each equivalence class for satisfiability is infeasable (for 12 variables there as as many
as xxx), even in the order sorted case where we can restrict ourselves to equivalences capatable
with the sort structure.

Instead we choose a darwainian approach, pruning classes of equivalences from the search space if
an identification of a single pair of variables implied by one theory is not satisfiable in another.
For the non-convex case, if any theory implies the disjunction of all remaining identifications
we branch our search, checking if atleast one of the remaining identifications is satisfiable.

$$\infer[\text{Equality Propagation}]
  { \begin{matrix*}[l]
          & \CheckSat(\phi_j \land \phi_E \land x_m = x_n) \\
    \land & \NelsonOppenSat(\phi_1 \land \phi_2 \land \phi_E, \CandidateEqualities \setminus \{x_m = x_n\})
    \end{matrix*}
  }
  { x_m = x_n \in \CandidateEqualities
  & T_i \models \phi_i \and \phi_E \implies x_m = x_n
  & \NelsonOppenSat(\phi_1 \land \phi_2 \land \phi_E, \CandidateEqualities)
  }
$$

$$\infer[\text{Split}]
  {\Or_{x_m = x_n \in \CandidateEqualities}
   \left(\begin{matrix*}[l]
        &      &\CheckSat(\phi_1 \land \phi_E \land x_m = x_n) \\
        &\land & \CheckSat(\phi_2 \land \phi_E \land x_m = x_n) \\
        &\land & \NelsonOppenSat(\phi_1 \land \phi_2 \land \phi_E, \CandidateEqualities \setminus \{x_m = x_n\})
   \end{matrix*}\right)
  }
  { 
  & T_i \models \phi_i \and \phi_E \implies \And \CandidateEqualities
  & \NelsonOppenSat(\phi_1 \land \phi_2 \land \phi_E, \CandidateEqualities)
  }
$$

\input{algorithm.tex}

Examples
========

* List + Rat example

Hereditarily Finite Sets parameterized over rationals
-----------------------------------------------------

\input{hfs.tex}

https://ac.els-cdn.com/S0167642317301788/1-s2.0-S0167642317301788-main.pdf?_tid=9fa3ca91-7528-400b-ab94-8a2efd43b4fc&acdnat=1523049049_18ce07f410687584e04ea942f15cafb7
7.5 21

Conclusion & Future work
========================

-   Keeping track of variant ctors
-   Integrating with SAT solver - Boolean struture
-   Shiney and Polite theories
    - bit vectors
