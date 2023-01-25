---
title: Abstract Reachability
subtitle: a semantics-based approach
author: Traian Florin Șerbănuță (with Virgil Șerbănuță and Dorel Lucanu)
institute: Runtime Verification
bibliography: k.bib
theme: RV
aspectratio: 169
header-includes:
- \usepackage{qrcode}
---

## Motivation for this research

- Algorithm for Reachability Logic Deduction for K
  + [@all-path-k]
- Idea to replace circular coinduction with regular induction
  + to allow proving total correctness
- I like formalizing mathematics with interactive provers
  + I don't trust my math technical skills anymore
- Fomalizing semantical notions is (a bit) easier

## Summary

- Formalization of transition systems and traces
- EF (exists finally) and AF (always finally) as fixpoints
- A (semantics) deduction system for the intersection between CTL and Reachability Logic
- Initial work on incorporating quantification
- Everything described here is formalized in Coq
  + and available on GitHub: \url{https://github.com/traiansf/arl-in-coq}
    \qrcode[hyperlink,height=0.5in]{https://github.com/traiansf/arl-in-coq}

# Related Logics

## Reachability Logic

- Program verification logic for K [@rl-original]
- Derives statements of the form $\varphi \Rightarrow \psi$
- Two flavors: one-path and all-paths

### One-path Reachability Logic [@rl-one-path]

Whenever starting in a configuration matching $\varphi$ there is always an execution
path leading to a configuration matching $\psi$

### All-paths Reachability Logic [@rl-all-paths]

A configuration matching $\psi$ will be reached on any execution path starting
in a configuration matching $\varphi$.

## Reachability Logic and CTL

### Resemblance

- one-path reachability formula: $\varphi \implies \mathop{EF} \psi$
- all-paths reachability formula: $\varphi \implies \mathop{AF} \psi$

### Differences

- CTL is richer
  + more temporal operators (AG, EG, AU, EU, ...)
- Reachability Logic is richer
  + Reachability formulae have structure and free variables

## Matching Logic is the best!

### Reachability Logic is richer than CTL
- Reachability formulae have structure and constraints

### Solution: Enter Matching Logic
- A logic mixing patterns and constraints
- Specifically designed to express matching for K
- Fixed-point operators ($\mu$, $\nu$) introduced to capture reachability
- Formulae interpreted as sets

# CTL $\cap$ RL

## Transition systems and traces

- A transition system is a set $D$ with a relation $\tau$ on it
- $a \in D$ is _reducible_ iff $\exists b, a \mathrel{\tau} b$
- A _transition sequence_ from $a$ to $b$ is 
  + a (finite) non-empty sequence of elements from $D$
  + such that any two consecutive elements are in relation $\tau$
  + its first element is $a$ and its last element is $b$ (can be equal)
- A _complete transition chain_ is
  + a (possibly infinite) non-empty sequence of elements from $D$
  + such that any two consecutive elements are in relation $\tau$
  + and the final element (if there is one) is irreducible
- the first element in a transition sequence/complete transition chain
  is called the _head_

## A set semantics for (a fragment) of CTL

- $\mathop{EX} B = \{ a \mid \exists b \in B, a \mathrel{\tau} b \}$ 
- $\mathop{AX} B = \complement{\left(\mathop{EX}{\left(\complement{B}\right)}\right)}$
- $\mathop{EF} B = \{ a \mid t \textit{ transition sequence from } a \textit{ to } b \textit{ and } b \in B \}$
- $\mathop{AF} B = \{ a \mid \forall t \textit{ complete transition chain}, \mathop{head} t = a \implies \exists b \in t, b \in B \}$

## EF and AF as fixed-points

### Exists-finally

- $\mathop{EF} \psi$ is the least-fixed-point of the functor
$$F_{\mathop{EF}}(X) = \psi \cup \{ a \mid \exists b \in X, a \mathrel{\tau} b \}$$

### Always-finally

- $\mathop{AF} \psi$ is the least-fixed-point of the functor
$$F_{\mathop{AF}}(X) = \psi \cup \{ a \mid \mathop{reducible} a \wedge \forall b, a \mathrel{\tau} b \implies b \in X \}$$

# Deduction Rules

## Reachability Claims in CTL

### One-path reachability

$\varphi \implies^{EF} \psi$

: defined as $\varphi \subseteq \mathop{EF}(\psi)$

### All-paths Reachability

$\varphi \implies^{AF} \psi$

: defined as $\varphi \subseteq \mathop{AF}(\psi)$


## Deduction rules for a reachability relation $R$

### Rule of Reflexivity

$$\frac{\checkmark }{\varphi \mathrel{R} \varphi}$$

### Rule of Transitivity

$$\frac{\varphi \mathrel{R} \psi \hspace{1em} \psi \mathrel{R} \chi}{\varphi \mathrel{R} \chi}$$

### Rule of Consequence

$$\frac{\varphi' \subseteq \varphi \hspace{1em} \varphi \mathrel{R} \psi \hspace{1em} \psi \subseteq \psi'}{\varphi' \mathrel{R} \psi'}$$

## Deduction Rules for a relation $R$

### Rule of Generalization

$$\frac{\varphi_i \mathrel{R} \psi \textrm{ for all } i \in I}{\bigcup_{i\in I}\varphi_i \mathrel{R} \psi}$$

### Rule of Disjunction (derivable from the above)

$$\frac{\varphi_1 \mathrel{R} \psi \hspace{1em} \varphi_2 \mathrel{R} \psi}{\varphi_1 \cup \varphi_2 \mathrel{R} \psi}$$

## Deduction Rules for a relation $R$

### Rule of one-path next

$$\frac{a \mathrel{\tau} b}{\{a\} \mathrel{R} \{b\}}$$

### Rule of all-paths next (derivable from one-path next and consequence)

$$\frac{\mathop{reducible} a}{\{ a \} \mathrel{R} \tau[\{a\}]}$$

## One-path and All-paths Reachability

### One-path Reachability

Definition

: $\varphi \implies^{EF} \psi \mathrel{::=} \varphi \subseteq \mathop{EF}(\psi)$

Rules sound for it

: Reflexivity, Transitivity, Consequence, Generalization, One-path next

### All-paths Reachability

Definition

: $\varphi \implies^{AF} \psi \mathrel{::=} \varphi \subseteq \mathop{AF}(\psi)$

Rules sound for it

: Reflexivity, Transitivity, Consequence, Generalization, All-paths next

# Reachability with structure

## Abstract terms, patterns, and predicates

- Fix an infinite (countable) set of _names_ $\mathcal V$
- A _valuation_ is a map from names to values (elements of $D$)
- A _term_ is a map from valuations to values
  + Yields exactly one value for each valuation of the names
- A _pattern_ is a map from valuations to sets of values
- A _predicate_ is a pattern such that
  + for each valuation it yields either $D$ or the empty set

## Dependence on a (finite) set of names

- Valuations $v$, $v'$ are _equivalent on $X \subseteq \mathcal{V}$_, written $v \equiv_X v'$ iff
  - $\forall x \in X, v(x) = v(x')$
- A (finite) subset of names $X \subseteq \mathcal{V}$ is _sufficient_ for term/pattern $t$ iff
  + for any $v$, $v'$ such that $v \equiv_X v'$, we have that $t(v) = t(v')$

## Abstract rewrite rules

$$\forall X, l \wedge \mathop{requires} \implies^{EX} r$$

- A set $X$ of names
- Terms $l$ and $r$, and a predicate _requires_ depending on $X$
- An _instance_ of the rule is the pair $(l(v), r(v))$
  + for any valuation $v$ such that $\mathop{requires}(v) \neq \emptyset$

### Transition system closed to rule

Any rule instance is in the $\tau$ relation.

### Transition system defined by set of rules

$a \mathrel{\tau} b$ iff there is a rule instance $(a, b)$


## Abstract Claim

$$\forall X, \varphi \wedge \mathop{requires} \implies^R \exists Z, \psi \wedge \mathop{insures}$$

- Sets $X$ and $Z$ of names
- pattern $\varphi$ and predicate _requires_ depending on $X$
- pattern $\psi$ and predicate _ensures_ depending on $X \cup Z$

### Intuition
- for any instance of the variables $X$,
- from any configuration described by $\varphi$ such that _requires_ holds
- *R = EF*: there exist a path such that / *R = AF*: on any path
- a configuration described by $\psi$ and satisfying _ensures_ will be reached
- for a particular instance of the variables $Z$ (potentially distinct for each path).

# Future work

##  Future work

- Redo the deduction systems for abstract claims
- Incorporate induction
- Documentation for the GitHub code
- Publish?


## References