#import "common.typ": *

= Preliminaries <sec-prelim>

== Traces

For the remainder of this article, let $bold("AP")$ be a finite and non-empty set of atomic propositions and
$Σ=2^bold("AP")$ a finite alphabet. We write $a_i$ for any single element of $Σ$. Finite traces over $Σ$ are elements of $Sigma^∗$, usually denoted with $u,u',u_1,u_2, dots$. The empty trace is denoted with ϵ. Infinite traces are elements of $Σ^ω$, usually denoted with $w, w', w_1, w_2, dots$ For some infinite trace $w = a_0a_1 ...$, we denote with $w^i$ the suffix $a_i, a_(i+1) dots$ . In case of a finite trace $u=a_0a_1 ...a_(n−1)$, $u^i$ denotes the suffix $a_i a_(i+1) ...a_(n−1)$ for $0 ≤ i < n$ and the empty string ϵ for $n ≤ i$.

== Truth domain

A lattice is a partially ordered set $(cal(L), ⊑)$ where for each $x,y ∈ cal(L)$, there exists (i) a unique greatest
lower bound (glb), which is called the meet of $x$ and $y$, and is denoted by $x ⊓ y$, and (ii) a unique
least upper bound (lub), which is called the join of $x$ and $y$, and is denoted by $x ⊔ y$. A lattice is called
finite iff $L$ is finite. Every finite lattice has a well-defined unique least element, called bottom, denoted
with $⊥$, and analogously a greatest element, called top, denoted with . A lattice is distributive, iff $x ⊓
(y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)$, and, dually, $x ⊔ (y ⊓ z)=(x ⊔ y) ⊓ (x ⊔ z)$. In a _de Morgan_ lattice, every element
$x$ has a unique dual element $overline(x)$, such that $overline(overline(x)) = x$ and $x ⊑ y$ implies $overline(y) ⊑ overline(x)$. A distributive lattice is called Boolean iff $x ⊔ overline(x) = ⊤$ and $x ⊓ overline(x) = ⊥$.
As the common denominator of the semantics for the subsequently defined logics is a finite de Morgan lattice, we take this to be our understanding of a truth domain.

We consider the traditional two-valued semantics that we denotes $bb(B)_2$ with truth values `true`, denoted with $top$, and `false`, denoted with $bot$. Truth values should be comparable and combinable in terms of Boolean operations expressed by the connectives of the underlying logic, we interpret these truth values as elements of a _de Morgan_ lattice.

#definition("Truth domain", label: <def:truth-dom>)[
  We call $cal(D)$ a _truth domain_, if it is a finite de Morgan lattice. The two valued truth domain $bb(B)_2 = { top, bot}$ is a Boolean lattice with the order $bot subset.sq top$ and $inter.sq$ and $union.sq$ defined in the expected manner.
]

== LTL and FLTL

== LTL

we first recall LTL interpreted over infinite traces, as introduced by Pnueli @ltl in the setting of specification and verification.
In case of LTL over infinite traces, one is used to have a syntax ranging over a small set of temporal and Boolean operators and to add additional operators by means of abbreviations.
The set of LTL formulae is defined using _true_, the atomic propositions $p ∈ bold("AP")$, disjunction, _next_ *X* and _until_ *U*, as positive operators, together with _negation_ ¬.
For comparison with logics over finite traces, we moreover add dual operators, namely false, $¬p$, weak next $overline(X)$ and release *R*, respectively.

#definition("Syntax of LTL formulae", label: <def:ltl-syntax>)[
  Let $p$ be an atomic proposition from a finite set of atomic propositions $bold("AP")$. The set of
  LTL formulae, denoted with LTL, is inductively defined by the following grammar:
  $
    φ & ::= "true" | p | φ or φ | φ until φ | bold(X) φ \
    φ & ::= "false" | ¬p | φ and φ | φ release φ | overline(bold(X)) φ \
    φ & ::= ¬φ
  $
]

Moreover, we define by means of abbreviation the _finally_ $bold(F)$ and _globally_ $bold(G)$
operators as

$ bold(F) φ := "true" until φ quad "and" quad bold(G) φ := ¬ bold(F) ¬φ $

as well as _implication_ $φ -> ψ$ as a shorthand for $¬φ or ψ$.
LTL formulae over infinite traces are interpreted as usual over the two valued truth domain
$bb(B)_2$.

#figure(
  placement: top,
  align(center)[
    #grid(
      columns: (auto, auto),
      column-gutter: 2.2em,
      row-gutter: 1.4em,
      align: left,
      [
        #fgrp[Boolean constants]
        $
           semw(w tack.rr "true") & = top \
          semw(w tack.rr "false") & = bot
        $
      ],
      [
        #fgrp[Boolean combinations]
        $
               semw(w tack.rr ¬φ) & = overline(semw(w tack.rr φ)) \
           semw(w tack.rr φ or ψ) & = semw(w tack.rr φ) union.sq semw(w tack.rr ψ) \
          semw(w tack.rr φ and ψ) & = semw(w tack.rr φ) inter.sq semw(w tack.rr ψ)
        $
      ],

      [
        #fgrp[atomic propositions]
        $
           semw(w tack.rr p) & = cases(
                                 top & "if " p in a_0,
                                 bot & "if " p in.not a_0
                               ) \
          semw(w tack.rr ¬p) & = cases(
                                 top & "if " p in.not a_0,
                                 bot & "if " p in a_0
                               )
        $
      ],
      [
        #fgrp[(weak) next]
        $
                    semw(w tack.rr bold(X) φ) & = semw(w^1 tack.rr φ) \
          semw(w tack.rr overline(bold(X)) φ) & = semw(w^1 tack.rr φ)
        $
      ],
    )

    #block(width: 100%)[
      #align(left, fgrp[until/release])
      $
        semw(w tack.rr φ until ψ) & = cases(
                                          gap: #.7em,
                                          #mcase(
                                            $top$,
                                            $"there is a " k >= 0 : semw(w^k tack.rr ψ) = top " and"$,
                                            $"for all " l " with " 0 <= l < k : semw(w^l tack.rr φ) = top$,
                                          ),
                                          #scase($bot$, $"else"$),
                                        ) \
                                      \
        semw(w tack.rr φ release ψ) & = cases(
                                          gap: #.7em,
                                          #mcase(
                                            $top$,
                                            $"for all " k >= 0 : semw(w^k tack.rr ψ) = top " or"$,
                                            $"there is a " k >= 0 : semw(w^k tack.rr φ) = top " and"$,
                                            $"for all " l " with " 0 <= l <= k : semw(w^l tack.rr ψ) = top$,
                                          ),
                                          #scase($bot$, $"else"$),
                                        )
      $
    ]
  ],
  caption: [Semantics of LTL formulae over an infinite traces $w = a_0 a_1 dots ∈ Σ^ω$],
) <fig-ltl-sem>

#definition("Semantics of LTL", label: <def:ltl-sem>)[
  The semantics of LTL formulae over infinite traces $w = a_0 a_1 dots ∈ Σ^ω$ is given by the
  function $lr(⟦ - tack.rr - ⟧)_ω : Σ^ω × "LTL" -> bb(B)_2$, which is defined inductively as shown
  in @fig-ltl-sem.
]

#remark[
  Inspecting the semantics, we observe that there is no difference of $bold(X)$ and
  $overline(bold(X))$ in LTL over infinite traces. However, $overline(bold(X))$ acts differently
  when finite traces are considered.
]

== FLTL

FLTL @rv-ltl is the interpretation of that same syntax (@def:ltl-syntax[-]) over a _finite_ trace,
still in $bb(B)_2$. Its semantics function is constructed like the one for standard LTL but with
two modifications: if a strong next-state operator in some subformula $bold(X) φ$ is referring to
a state beyond the known finite prefix $u$, then this subformula is evaluated to $bot$, regardless
of $φ$. Likewise, a subformula $overline(bold(X)) φ$ always evaluates to $top$ if it refers to a
state beyond $u$. This approach is extended to the definition of the until and release operators.
For example, to satisfy $φ until ψ$ with a finite trace $u$, there must exist a position
satisfying $ψ$ within $u$.

#figure(
  placement: top,
  align(center)[
    #block(width: 100%)[
      #align(left, fgrp[(weak) next])
      $
                  semf(u tack.rr bold(X) φ) & = cases(
                                                semf(u^1 tack.rr φ) & "if " u^1 != ϵ,
                                                bot & "otherwise"
                                              ) \
                                            \
        semf(u tack.rr overline(bold(X)) φ) & = cases(
                                                semf(u^1 tack.rr φ) & "if " u^1 != ϵ,
                                                top & "otherwise"
                                              )
      $

      #align(left, fgrp[until/release])
      $
        semf(u tack.rr φ until ψ) & = cases(
                                          gap: #.7em,
                                          #mcase(
                                            $top$,
                                            $"there is a " k ∈ {0, dots n-1} : semf(u^k tack.rr ψ) = top " and"$,
                                            $"for all " l " with " 0 <= l < k : semf(u^l tack.rr φ) = top$,
                                          ),
                                          #scase($bot$, $"else"$),
                                        ) \
                                      \
        semf(u tack.rr φ release ψ) & = cases(
                                          gap: #.7em,
                                          #mcase(
                                            $top$,
                                            $"for all " k ∈ {0, dots n-1} : semf(u^k tack.rr ψ) = top " or"$,
                                            $"there is a " k ∈ {0, dots n-1} : semf(u^k tack.rr φ) = top " and"$,
                                            $"for all " l " with " 0 <= l <= k : semf(u^l tack.rr ψ) = top$,
                                          ),
                                          #scase($bot$, $"else"$),
                                        )
      $
    ]
  ],
  caption: [Semantics of FLTL formulae over a trace $u = a_0 dots a_(n-1) ∈ Σ^*$],
) <fig-fltl-sem>

#definition("Semantics of FLTL", label: <def:fltl-sem>)[
  Let $u = a_0 dots a_(n-1) ∈ Σ^*$ denote a finite trace of length $n$, with $u != ϵ$. The truth
  value of an FLTL formula $φ$ w.r.t. $u$, denoted with $semf(u tack.rr φ)$, is an element of
  $bb(B)_2$ and is inductively defined as follows: Boolean constants, Boolean combinations and
  atomic propositions are defined as for LTL (see @fig-ltl-sem, taking $u$ instead of $w$).
  Until/release and (weak) next are defined as shown in @fig-fltl-sem.
]
