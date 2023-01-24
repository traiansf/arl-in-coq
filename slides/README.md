---
title: Abstract Reachability
subtitle: a semantics-based approach
author: Traian Florin Șerbănuță (joint work with Virgil Șerbănuță and Dorel Lucanu)
institute: Runtime Verification
bibliography: k.bib
theme: RV
aspectratio: 169
---

## Motivation for this research

- Algorithm for Reachability Logic Deduction for K
  + with Virgil Șerbănuță and Xiaohong Chen
- Idea to replace circular coinduction with regular induction
  + to allow proving total correctness
- I like formalizing mathematics with interactive provers
  + I don't trust my math technical skills anymore
- Fomalizing semantical notions is (a bit) easier

## Results (so far)

- Formalization of transition systems and traces
- EF (exists finally) and AF (always finally) as fixpoints
- A (semantics) deduction system for the intersection between CTL and Reachability Logic
- Initial work on incorporating quantification

# Preliminaries

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

# Technical preliminaries

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
- $\mathop{EF} B = \{ a \mid t \textit{ transition system from } a \textit{ to } b \textit{ and } b \in B \}$
- $\mathop{AF} B = \{ a \mid \forall t \textit{ complete transition chain}, \mathop{head} t = a \implies \exists b \in t, b \in B \}$

## Exists-finally and Always-finally as fixed-points

### Exists-finally

- $\mathop{EF} \psi$ is the least-fixed-point of the functor
$$F_{\mathop{EF}}(X) = \psi \cup \{ a \mid \exists b \in X, a \mathrel{\tau} b \}$$

### Always-finally

- $\mathop{AF} \psi$ is the least-fixed-point of the functor
$$F_{\mathop{AF}}(X) = \psi \cup \{ a \mid \mathop{reducible} a \wedge \forall b, a \mathrel{\tau} b \implies b \in X \}$$

# Deduction Rules

## Deduction Rules for a relation $R$

Rule of Reflexivity

: $\displaystyle\frac{\checkmark }{\varphi \mathrel{R} \varphi}$

Rule of Transitivity

: $\displaystyle\frac{\varphi \mathrel{R} \psi \hspace{1em} \psi \mathrel{R} \chi}{\varphi \mathrel{R} \chi}$

Rule of Consequence

: $\displaystyle\frac{\varphi' \subseteq \varphi \hspace{1em} \varphi \mathrel{R} \psi \hspace{1em} \psi \subseteq \psi'}{\varphi' \mathrel{R} \psi'}$

## Deduction Rules for a relation $R$

Rule of Disjunction

: $\displaystyle\frac{\varphi_1 \mathrel{R} \psi \hspace{1em} \varphi_2 \mathrel{R} \psi}{\varphi_1 \cup \varphi_2 \mathrel{R} \psi}$

Rule of Generalization

: $\displaystyle\frac{\varphi_i \mathrel{R} \psi \textrm{for all } i \in I}{\bigcup_{i\in I}\varphi_i \mathrel{R} \psi}$

## Deduction Rules for a relation $R$



## References