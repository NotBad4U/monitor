#import "common.typ": *

= Timed RV-LTL <sec-timed-rvttl>

#let timed-word = $
  rho = (σ_1, tau_1) dots (σ_(abs(rho)), tau_(abs(rho))) ∈ (Σ × RR_(>= 0))
$

#let timed-word-mono = $tau_k <= tau_(k+1)$

#definition([Timed word], label: <def:timed-word>)[
  A _timed word_ over $Σ$ is a sequence
  #timed-word
  of letters $σ_k ∈ Σ$ paired with timestamps $tau_k ∈ RR_(>= 0)$, whose timestamps are
  non-decreasing: #timed-word-mono. We write $rho^j$ for the suffix $(σ_j, tau_j) dots (σ_(abs(rho)), tau_(abs(rho)))$
  ,and write $rho(i) = (σ_i, tau_i)$.
]

== Metric RV-LTL

#let mfltl4 = `MFLTL₄`
#import mannot: mark, markhl, annot

The #mfltl4 is an extension of #fltl4 in which temporal operators are replaced by time-constrained versions like until $(bold(U)_I)$, next $(bold(X)_I)$ operators.
It is a linear-time logic that assumes both the interleaving and fictitious-clock abstractions.
It is defined over a point-based weakly monotonic discrete non-negative time semantics.

#let mfltl4-syntax = $
  φ, ψ ::= top | bot | p | ¬ φ | φ and ψ | φ until_I ψ | φ release_I ψ | bold(X)_I φ | bold(overline(X))_I φ
$

#definition([Syntax of #mfltl4], label: <def:metric-fltl4-syntax>)[
  Let $Σ = 2^bold("AP")$ be the finite alphabet built over a finite set of atomic
  propositions $bold("AP")$, with $p ∈ bold("AP")$ an atomic proposition. Let
  $overline(RR)_(>= 0) = RR_(>= 0) ∪ {∞}$ be the extended non-negative reals, and let
  $a ∈ RR_(>= 0)$ and $b ∈ overline(RR)_(>= 0)$ with $a <= b$ be the bounds of a time interval $I = [a, b]$.
  The set of #mfltl4 formulae is inductively defined by the following grammar:
  #mfltl4-syntax
  We denote the subscript $-_(I)$, with $I = [a, b]$, when it is not necessary to specify the endpoints $a$ and $b$.
]

#let mfltl4-sem = align(center)[
  #grid(
    columns: (auto, auto),
    column-gutter: 2.2em,
    row-gutter: 1.4em,
    align: left,
    [
      #fgrp[Boolean constants]
      $
        sem(rho comma i tack.rr top) & = top \
        sem(rho comma i tack.rr bot) & = bot
      $
    ],
    [
      #fgrp[Boolean combinations]
      $
             sem(rho comma i tack.rr ¬φ) & = overline(sem(rho comma i tack.rr φ)) \
        sem(rho comma i tack.rr φ and ψ) & = sem(rho comma i tack.rr φ) inter.sq sem(rho comma i tack.rr ψ)
      $
    ]
  )
  #block(width: 100%)[
    #align(left, fgrp[atomic propositions])
    $
        sem(rho comma i tack.rr p) & = cases(
                                      top & "if " p in σ_i,
                                      bot & "if " p in.not σ_i
                                    )
        quad quad
        sem(rho comma i tack.rr ¬p) & = cases(
                                      top & "if " p in.not σ_i,
                                      bot & "if " p in σ_i
                                    )
    $
  ]
  #block(width: 100%)[
    #align(left, fgrp[(weak) next])
    $
                sem(rho comma i tack.rr bold(X)_(I) φ) & = cases(
                                                            sem2(tau_(i+1) - tau_i ∈ I) inter.sq sem(rho comma i+1 tack.rr φ) & "if " i < abs(rho),
                                                            bot^p & "if " i = abs(rho)
                                                          ) \
      sem(rho comma i tack.rr overline(bold(X))_(I) φ) & = cases(
                                                            sem2(tau_(i+1) - tau_i ∈ I) inter.sq sem(rho comma i+1 tack.rr φ) & "if " i < abs(rho),
                                                            top^p & "if " i = abs(rho)
                                                          )
    $
  ]
  #block(width: 100%)[
    #align(left, fgrp[until/release])
    $
        sem(rho comma i tack.rr φ until_(I) ψ) & = union.sq.big_(i <= j <= abs(rho)) (
                                                    sem2(tau_j - tau_i ∈ I)
                                                    inter.sq sem(rho comma j tack.rr ψ)
                                                    inter.sq inter.sq.big_(i <= k < j) sem(rho comma k tack.rr φ)
                                                  ) \
                                                & quad union.sq (
                                                    bot^p
                                                    inter.sq sem2(tau_(abs(rho)) <= tau_i + b)
                                                    inter.sq inter.sq.big_(i <= k <= abs(rho)) sem(rho comma k tack.rr φ)
                                                  ) \
                                                \
      sem(rho comma i tack.rr φ release_(I) ψ) & = inter.sq.big_(i <= j <= abs(rho)) (
                                                    sem2(tau_j - tau_i in.not I)
                                                    union.sq sem(rho comma j tack.rr ψ)
                                                    union.sq union.sq.big_(i <= k < j) sem(rho comma k tack.rr φ)
                                                  ) \
                                                & quad inter.sq (
                                                    top^p
                                                    union.sq sem2(tau_(abs(rho)) > tau_i + b)
                                                    union.sq union.sq.big_(i <= k <= abs(rho)) sem(rho comma k tack.rr φ)
                                                  )
    $
  ]
]

#figure(
  placement: top,
  mfltl4-sem,
  caption: [Semantics of #mfltl4 formulae over a timed word $rho$ at position $i$.],
) <fig-mfltl4-sem>

#let mfltl4-sem-sig = $sem(rho comma i tack.rr phi) : (Σ × RR_(>= 0))^+ × NN × #mfltl4 -> bb(B)_4$

#definition([Valuation of #mfltl4], label: <def:mfltl4-sem>)[
  An #mfltl4 formula $φ$ hold at time $t$ with a timed word $rho$ and
  $1 <= i <= abs(rho)$. The _valuation_ #mfltl4-sem-sig
  is defined inductively on $φ$ in @fig-mfltl4-sem. Its until clause reads
  #v(1.6em)
  $
    sem(rho comma i tack.rr φ until_(I) ψ)
      & = union.sq.big_(i <= j <= abs(rho)) (
            mark(sem2(tau_j - tau_i ∈ I), #<g-observed>, #cteal)
            inter.sq sem(rho comma j tack.rr ψ)
            inter.sq inter.sq.big_(i < k < j) sem(rho comma k tack.rr φ)
          ) \
      & quad union.sq (
            bot^p
            inter.sq mark(sem2(tau_(abs(rho)) <= tau_i + b), #<g-pending>, #cpurpD)
            inter.sq inter.sq.big_(i <= k <= abs(rho)) sem(rho comma k tack.rr φ)
          )
    #annot(<g-observed>, pos: top, dx: 3em, dy: -1em, leader-connect: "elbow")[events for $I$ observed]
    #annot(<g-pending>, pos: bottom, dx: 3em, dy: 0.5em, leader-connect: "elbow")[pending on missing events]
  $
]

#let mfltl4-abbrev = [
  - $φ or ψ := ¬(¬φ and ¬ψ)$
  - $bold(F)_(I) φ := top until_(I) φ$
  - $bold(G)_(I) φ := ¬ bold(F)_(I) ¬φ$
]

#remark[
  The remaining operators are abbreviations:
  #mfltl4-abbrev
]

#proposition[
  For $a = 0$ and $b = ∞$, #mfltl4 is a conservative extension of #fltl4.
]

#place.flush()


== Timed Propositional RV-LTL

#let tfptl4 = `TFPTL₄`
#let opn = $op("open")$
#let cmp = $class("normal", ⋈)$ // a comparison among <, ≤, =, ≥, >

#tfptl4 extends #fltl4 with explicit references to time in the formula.
Variables are introduced to measure times between two events.


#let tfptl4-syntax = $
  φ, ψ ::= top | bot | p | x ⋈ c | ¬ φ | φ and ψ | x. φ | φ until ψ | φ release ψ | bold(X) φ | bold(overline(X)) φ
$

#definition([Syntax of #tfptl4], label: <def:tfptl4-syntax>)[
  Let $Σ = 2^bold("AP")$ be the finite alphabet built over a finite set of atomic
  propositions $bold("AP")$, with $p ∈ bold("AP")$ an atomic proposition. Let $cal(V)$
  be a set of _clock variables_, with $x ∈ cal(V)$, let $c ∈ RR_(>= 0)$ be a constant
  and let $cmp ∈ {<, ≤, =, ≥, >}$ be a comparison. The set of #tfptl4 formulae is
  inductively defined by the following grammar:
  #tfptl4-syntax
  A formula is name _closed_ when each of its time constraints $x ⋈ c$ occurs under a freeze quantifier $x.$ of the same variable.
]

#let tfptl4-sem = align(center)[
  #grid(
    columns: (auto, auto),
    column-gutter: 2.2em,
    row-gutter: 1.4em,
    align: left,
    [
      #fgrp[Boolean constants]
      $
        sem(rho comma i comma nu tack.rr top) & = top \
        sem(rho comma i comma nu tack.rr bot) & = bot
      $
    ],
    [
      #fgrp[Boolean combinations]
      $
             sem(rho comma i comma nu tack.rr ¬φ) & = overline(sem(rho comma i comma nu tack.rr φ)) \
        sem(rho comma i comma nu tack.rr φ and ψ) & = sem(rho comma i comma nu tack.rr φ) inter.sq sem(rho comma i comma nu tack.rr ψ)
      $
    ]
  )
  #block(width: 100%)[
    #align(left, fgrp[atomic propositions])
    $
        sem(rho comma i comma nu tack.rr p) & = cases(
                                               top & "if " p in σ_i,
                                               bot & "if " p in.not σ_i
                                             )
        quad quad
        sem(rho comma i comma nu tack.rr ¬p) & = cases(
                                               top & "if " p in.not σ_i,
                                               bot & "if " p in σ_i
                                             )
    $
  ]
  #block(width: 100%)[
    #align(left, fgrp[time constraints and freeze])
    $
      sem(rho comma i comma nu tack.rr x ⋈ c) & = sem2(tau_i - nu(x) ⋈ c) \
       sem(rho comma i comma nu tack.rr x. φ) & = sem(rho comma i comma nu[x |-> tau_i] tack.rr φ)
    $
  ]
  #block(width: 100%)[
    #align(left, fgrp[(weak) next])
    $
                sem(rho comma i comma nu tack.rr bold(X) φ) & = cases(
                                                               sem(rho comma i+1 comma nu tack.rr φ) & "if " i < abs(rho),
                                                               bot^p & "if " i = abs(rho)
                                                             ) \
      sem(rho comma i comma nu tack.rr overline(bold(X)) φ) & = cases(
                                                               sem(rho comma i+1 comma nu tack.rr φ) & "if " i < abs(rho),
                                                               top^p & "if " i = abs(rho)
                                                             )
    $
  ]
  #block(width: 100%)[
    #align(left, fgrp[until/release])
    $
        sem(rho comma i comma nu tack.rr φ until ψ) & = union.sq.big_(i <= j <= abs(rho)) (
                                                       sem(rho comma j comma nu tack.rr ψ)
                                                       inter.sq inter.sq.big_(i <= k < j) sem(rho comma k comma nu tack.rr φ)
                                                     )
                                                     union.sq (
                                                       bot^p
                                                       inter.sq inter.sq.big_(i <= k <= abs(rho)) sem(rho comma k comma nu tack.rr φ)
                                                     ) \
                                                     \
      sem(rho comma i comma nu tack.rr φ release ψ) & = inter.sq.big_(i <= j <= abs(rho)) (
                                                       sem(rho comma j comma nu tack.rr ψ)
                                                       union.sq union.sq.big_(i <= k < j) sem(rho comma k comma nu tack.rr φ)
                                                     )
                                                     inter.sq (
                                                       top^p
                                                       union.sq union.sq.big_(i <= k <= abs(rho)) sem(rho comma k comma nu tack.rr φ)
                                                     )
    $
  ]
]

#figure(
  placement: top,
  tfptl4-sem,
  caption: [Semantics of #tfptl4 formulae over a timed word $rho$ and a clock valuation $nu$.],
) <fig-tfptl4-sem>

#let clock-valuation = $nu : cal(V) -> RR_(>= 0)$

#definition([clock])[
  A _clock valuation_ #clock-valuation gives, for each clock variable, the
  time instant at which it was frozen; $nu[x |-> t]$ maps $x$ to $t$ and agrees with $nu$
  on the other variables. 
]

#let tfptl4-sem-sig = $sem(rho comma i comma nu tack.rr phi) : (Σ × RR_(>= 0))^+ × NN × (cal(V) -> RR_(>= 0)) × #tfptl4 -> bb(B)_4$

#definition([Semantics of #tfptl4], label: <def:tfptl4-sem>)[
  An #tfptl4 formula $φ$ holds at time $i$ on a timed word $rho$ under a clock valuation $nu$. The valuation function is written #tfptl4-sem-sig
  which is defined inductively in @fig-tfptl4-sem.
]


#proposition[
  #tfptl4 is a conservative extension of #fltl4: the two semantics coincide on formulae
  without freeze quantifiers and time constraints.
]
