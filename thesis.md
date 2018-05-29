---
title: "Order-Sorted Nelson-Oppen Combination in Rewriting Logic"
author: Nishant Rodrigues
advisor: Dr. Jose Meseguer
year: 2018
department: Mathematics
schools: University of Illinois at Urbana-Champaign
---

\newcommand \braces[1] {\{ #1 \}}

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

\newcommand \purified        {\And\Lit(\Sigma_1) \land \And\Lit(\Sigma_2) \land \Lit(\Sigma_0)}
\newcommand \arrangements    {\Or\{\ \}}

\newcommand \SharedSorts     {S_0}
\newcommand \SharedVariables {X^{1, 2}}
\newcommand \onetwo {\{1, 2\}}
\newcommand \Equiv {\text{Equiv}}

\renewcommand \phi {\varphi}

\newcommand \NelsonOppenSat {\text{NelsonOppenSat}} 
\newcommand \CheckSat       {\text{CheckSat}} 
\newcommand \CandidateEqualities {\text{CE}} 

\pagebreak

Introduction
===========

The Maude programming language is based on rewriting logic. It is often used for modeling and
verification of systems. It has been used to verify a wide spectrum of systems, from biological
systems (Pathway Logic [@pathwaylogic]), to Network Protocols (Maude NPA [@NPA]), to concensus algorithms,
and programming languages (KFramework [@kmaude]).

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

In [@nelsonoppen], the first general algorithm for deciding the satisfiability of
formulae in the union of two theories, provided they meet two conditions:

1.  The theories are "stably infinite"
2.  Their signatures are disjoint.

Later, in [@tinelliordersorted], this algorithm was generalized and formalized for order-sorted
logics. This was further refined and concretized in [@cs576] into a
system of inference rules.

Logical Foundations of Maude
============================

Maude is based on two logics, one contained in the other. 

The first, equational logic, is the Horn logic fragment of first-order logic with equality for
signatures involving only function symbols. The second, rewriting logic, is defined by transitions
between equivalence classes of terms defined by an equational theory.

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

The expressiveness of Equational Logic can be tuned by allowing
signatures to carry more or less information. In *many-sorted*
equational logic, each function symbol is also attached to a list of
_argument sorts_ $s_1, s_2, \ldots, s_n$, and a _result sort_ $s$.
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
The sentences that $\mathcal R$ proves are obtained from the finite application of the following
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

For a more in-depth look at rewriting logic, see [@twentyears].

Maude
-----

The programming language, Maude, is based on rewriting logic.
A program in Maude is a rewrite theory, and a computation is a deduction based
on the inference rules above. A basic introduction to Maude follows. For a more
thorough guide see [@maudemanual].

An equational theory is specified as a _functional modules_:

```
fmod Z5 is
    protecting BOOL .

    sorts Z5 .
    op 0 : -> Z5                              [ctor] .
    op 1 : -> Z5                              [ctor] .
    op _ + _ : Z5 Z5 -> Z5   [assoc comm id: 0 ctor] .
    op _ * _ : Z5 Z5 -> Z5   [assoc comm id: 1     ] .

    vars x y : Z5 .

    --- Characteristic 5
    eq 1 + 1 + 1 + 1 + 1 = 0     .

    --- Define multiplication in terms of repeated multiplication
    eq x * 0 = 0                 .
    eq x * (1 + y) = x + (x * y) .
endfm
```

This program represents an equational theory $E = ((S, \le_S), \Sigma, E \union B)$. Here,
$S = \braces{\tt Z5}\, \le_s = \braces{{\tt NzZ5}, {\tt Z5}}$ and
$\Sigma = \braces{ {\tt 0}, {\tt 1}, {\tt \_ + \_}}$.
The `fmod Z5 is ... endfm` construct defines a *functional module* and describes an equational
theory. The signature of this theory has a single sort `Z5` The `op` declaration defines the
terms and functions in the signature of that theory. These are of the form
`op NAME : ARGUMENTS -> RESULT [ATTRIBUTES]`. For example, `_ + _` takes two terms of sort `Z5` and
returns another of the same sort, while `0` and `1` are constants of sort `Z5`. The `ctor` attribute
marks a term as part of the constructor signature of the theory. The `assoc`, `comm` and `id: 0`
attributes mark the plus operator as being associative, commutative and having `0` as its identity.
The `vars` declaration allows using the tokens `x` and `y` as variables in equations. Each `eq`
construct represents an axiom in the equational theory.

The `protecting BOOL` declaration includes the `BOOL` equational theory as a subtheory. Programmers
must be careful not to alter the semantics of protected theories, e.g. by adding an equation
`eq true = false .`

Although ordinarily equations in equational theories are symmetric -- in a proof we may replace
equals by equals if a term matches either the left hand side or the right hand side -- equations in
Maude are only applied from left to right. This is to allow defining a terminating execution.
Attributes like `assoc` and `comm` allow specifying common axioms that would be difficult to define
in a non-terminating way (and also make implementation of Maude's matching and unification
algorithms easier and more efficient.) Because of this directionality, the theories must be
*confluent* for them to form a well-defined equational theory. i.e. the application of equations must yield
the same final result irrespective of the order in which they are applied. Although tools such as
the Church-Rosser Checker and the Maude Termination Tool are provided, the burden of defining
confluent and terminating functional modules is ultimately on the programmer defining them. The
orientation on the equations means that we will sometimes have to define equations that would
otherwise be mathematically deducible.

Defining a program as above means that there is an extremely small representational distance between
the programs and the mathematical logic we use to reason about them.

### Maude Meta Level

Rewriting logic is a *reflective logic* -- its meta theory can be represented at the object level in
a consistent way. i.e. there is a *universal theory* $U$ and a function
$\overline { ( \_ \proves \_ ) }$ such that for any theory $T$,
$T \proves \phi \iff U \proves \overline{ T \proves \phi }$.

In Maude, the built-in module `META-LEVEL` is used to do this lifting. Terms are represented in the
sort `Term`, and modules in the sort `Module`. The function
`upModule : ModuleExpression Bool -> Module` takes a `ModuleExpression`, a quote follows by the
module name (e.g. `'Z5`) and returns a term representing the module. Similarly, the function
`upTerm : Universal -> Term` takes a term of any sort and returns a meta-term of sort `Term`.
Terms at the meta-level are represented using quoted identifiers. Arguments to terms are
placed in a comma separated list within square brackets. Constants and variables have
their sorts annoted as part of the identifier. For example the term `1 + 1` is represented
at the meta level as `'_+_[ '1.Z5, '1.Z5 ]`, while the variable `X` as `'X:Z5`.
Meta-terms can be reduced using the `metaReduce` function.

`META-LEVEL`'s
`upModule` function allows us to lift a theory and perform rewrites with
it like any other term.

[Reflection in General Logics, Rewriting Logic and Maude]:
https://www.sciencedirect.com/science/article/pii/S1571066105825538

### Decision Procedures in Maude

Some satisfiability procedures have been been implemented in Maude using the `META-LEVEL`. We will
use these solvers as the subsolvers for Nelson-Oppen.

#### Variant-based Satisfiability

Variant-based satisfiability is a theory-generic procedure that applies to
a large set of user-definable order-sorted signature. The equations of this
theory must satisfy the *finite variant property* and may include axioms such as
commutativity, associativity-commutativity or identity.
Refer to [@varsat] for a more in-depth description.

Let $T = (\Sigma, E \union B)$ where the equations $E$ are confluent, terminating and $B$-coherent
modulo axioms. A $E,B-$variant of a term $t$ is a pair $(u, \theta)$ such that
$u =_B (t\theta)!_{\vec E,B}$, where for any term $u$, $u!_{\vec E, B}$ denotes the fully simplified
term obtained by exhaustive simplification with the oriented equations $\vec E$ modulo $B$. Given
variants $(u, \theta)$ and $(v, \gamma)$ of $t$, $(u, \theta)$ is more general than $(v, \gamma)$
iff there is a substitution $\rho$ such that:

1. $\theta\rho =_B \gamma$ and
2. $u\rho =_B v$

A theory $T$ has the finite variant property (FVP) iff for each term $t$ there is a finite most
general complete set of variants. If a theory $(\Sigma, E\union B)$ is FVP and $B$ has a finitary
$B-$unification algorithm, then folding variant narrowing gives a finitary $E\union B$-unification
algorithm [@XXX].

Furthermore, if $(\Sigma, E \union B) \supseteq (\Omega, E_{\Omega} \union B_\Omega)$ is a subsignature of constructors and
$(\Omega, E_{\Omega} \union B_\Omega)$ is OS-compact,
then satisfiability of quantifier free formulae in this theory are decidable by variant-based
satisfiablity. This has been implmented in Maude by Sherik and Meseguer[@metalevelvarsat]
and will be used for demonstrating the order-sorted Nelson-Oppen combination method.

#### CVC4

CVC4 is an industry-standard automatic theorem prover for SMT problems that supports many theories
including rational and integer linear arithmetic, array, bitvectors and a subset of non-linear
arithmetic. Although CVC4 allows defining algebraic data types it does not allow these user-defined
types to have equations over them. Thus its power can clearly be augmented by combination with
variant-based satisfiability.

Order Sorted Nelson Oppen as a rewrite theory
=============================================

Conditions on the theories
--------------------------

For the Nelson Oppen method to be viable, the order-sorted theories must meet the following conditions:

1.  They must be stably infinite
2.  They must be optimally intersecting.

Stably Infinite

:   Let $T$ be an order-sorted first-order theory with signature $\Sigma = ((S, \le), F, P)$ and
    $s_1, s_2,\ldots s_n \in S$. Let $\F \subset \FO(\Sigma)$, be the set of first order formulae in
    $\Sigma$

    $T$ is stably infinite in sorts $s_1, s_2,\ldots s_n$ for $\F-$satisfiability iff every
    $T-$satisfiable formula $\phi \in \F$, is also satisfiable in a model
    $\mathcal B = (B, \__B) \in \model(T)$ such that $|B_{s_i}| \ge \chi_0, 1 \le i \le n$.

    Intuitively, it means that we can always find models of both theories where the cardinalities
    of sorts $s_1, \ldots, s_n$ agree.

Notation: For sort $s$ and signature $\Sigma_i$, let $[s]_i$ denote it's
connected component of sorts in $\Sigma_i$

Optimally intersectable [@cs576]

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
            top-sort of at least one of the connected components.

        iii. **Once component is subsumed in the other:**

             a.  $\exists k \in \onetwo$ and $[s_k]_k$ has a top sort,
                 $[s_k]_k \subset [s_l]_l$ $\{k, l\} = \onetwo$.
             b.  $\le_k \intersect [s_k] = \le_l \intersect [s_k]_2^2$
             c.  (downward closure):
                 $\forall s \in [s_l]_l, \forall s' \in [s_k]_k, s\le_l s' \implies s\in [s_k]_k$

Overview
--------

Given two order-sorted, optimally intersecting, stably-infinite theories $T_1$ and $T_2$ with
signatures $\Sigma_1$ and $\Sigma_2$ each with decision procedures for quantifier free
$T_i$-satisfiability we want to derive a decision procedure for quantifier free $T_1 \union T_2$
satisfiability.

We can transform any formula $\phi$ into an *equisatisfiable* formula in disjunctive normal form.
Further, for each atom in such a formula we can apply "purification" to obtain a formula where each
atom is in the signature of one of the two theories.

Now, our task has become to find a model $M_0$ and an assignment $a: \vars(\phi) \to M_0$ such that
$M_0, a \models \purified$, where $\Sigma_0$ is the intersection of the two signatures. In general,
this requires knowing the semantics of each of the theories, but in the case of stably infinite
theories, the task is easier. With stable infiniteness, since every satisfiable formula has an
infinite model, if we need a value distinct from a witness we have infinite choices for either the
value or the witness. i.e. $$T_1 \union T_2 \not\models \phi \land \vec t_k \ne \vec t'_k 
\iff T_i \models \phi \limplies \vec t_k = \vec t'_k$$ This means that we do not need to find a
specific arrangement, but just a satisfiable equivalence relation of the shared variables. For any
formula, $\purified$, we have an equisatisfiable formula
$\Or_{equiv\in \Equiv(\SharedVariables)}\{ \purified \land \phi_{\equiv}\}$, where
$\Equiv(\SharedVariables)$ is the set of partitions on the shared variables $\SharedVariables$ and
$\phi_\equiv$ is the formula defining this equivalence relation. Since for stably infinite theories
we only care about the equivalence class being satisfiable, we can project this formula onto each of
the theories and check satisfiability.

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
but do not yet have a viable efficient algorithm. Checking each equivalence class for satisfiability
is infeasable as the number of equivalence classes grows exponentially with the number of variables,
even in the order sorted case where we can restrict ourselves to equivalences capatable with the
sort structure.

Instead we choose a Darwinian approach, pruning classes of equivalences from the search space if
an identification of a single pair of variables implied by one theory is not satisfiable in another.
For the non-convex case, if any theory implies the disjunction of all remaining identifications
we branch our search, checking if at least one of the remaining identifications is satisfiable.

We can think of each step of the algorithm as splitting the search space into subsets where
a single additional identification holds. If only a single identification is implied equality propagation
causes the algorithm to decend into it. Otherwise, the split rule checks the satisfiability of each of the sets
in the split subspaces, and decends into each satisfiable one.

### Order-Sorted Nelson-Oppen as a Rewrite Theory

\input{algorithm.tex}

Examples
========

Uninterpreted functions
-----------------------

\input{uninterp.tex}

Combining Lists with Integers
-----------------------------

\input{list-nat.tex}

Hereditarily Finite Sets parameterized over rationals
-----------------------------------------------------

\input{hfs.tex}

<!--
Matrices
--------

\input{matrix.tex}
-->

Conclusion & Future work
========================

The examples above have demonstrated the usefulness of Nelson-Oppen combination in Maude. Even so,
the tool is still a prototype. There are several avenues that need to be explored before fully
exploiting its potential. An obvious generalization is to handle combinations of more than two
theories. One obvious and simple generalization to make is to have the module take more than two
theories. Another is to accept a wider variaty of theories. 

Stable infiniteness requires that the theory has infinite models. However, there are several
important theories that are not stably infinite. For example, the theory of bit vectors
($\Z / 2^n\Z$) can be used to model "machine integers" widely used in many programming languages. In
[shiny], Tinelli and Zarba showed that this requirement can be reduced to the case where all but one
of the theories is "shiny". Further work by Ranise, Ringeissen and Zarba[@polite], and by Jovanovi
and Barrett[@politerevisited] provided an easier to compute alternative called strongly "polite"
theories. Extending this implementation to handle these cases would greatly expand the usefulness of
these theories.

Being a prototype, little effort has been spent on optimization. For example, when working with the
`var-sat` solver, the list of most general unifiers is computed repeatedly at every at every query
to the solver. Computing this list can be expensive depending on the term and theory under
consideration. For example, in an extreme case the term
`{ X:Magma, Y:Magma, Z:Magma } C= { X:Magma }` took tens of minutes to compute.

Another possible optimization is to take advantage of the propositional structure of the formula
through combination with a boolean SAT solver. The DPLL is an algorithm for deciding the
satisfiablilty of propositional logic formulae and forms the basis of most modern efficient solver
[@krstic2007architecting].

In general, one can envision incrementally building up towards a flexible, efficient and powerful
SMT infrastructure in Maude delegating both to external solvers as well as tools leveraging the
power and expressiveness of rewriting logic.

References
==========

