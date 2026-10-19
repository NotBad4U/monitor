#import "common.typ": *

= The logic #fltl4 <sec-fltl4>

FLTL interprets LTL formulae over finite traces.
That is the right reading for a _completed_ run of a program that terminated and where no more new events are expected. However, it is a wrong approach for runtime verification, where the trace in hand is a _prefix_ of a run still being produced, i.e. the next event has not arrived yet.
Two failures follow:
- the strong next $bold(X) phi$ has to infer;
- and a two-valued verdict can never be provisional.

The second aspect shows that with only $top$ and $bot$ available, every verdict is final.
A two-valued semantics must commit after each event even when the run could still go either way.
Take the request/acknowledge property $φ ≡ bold(G) (r -> bold(F) a)$ of @fig-futures. If the prefix
ends on a request $r$, FLTL evaluates $phi$ to $bot$, but it is too early to say that. $bot$ reads as
_the property is violated_, whereas here we are simply still waiting for the acknowledgement $a$,
which may well arrive later. The honest answer is not a definitive false but something weaker:
_false so far_, or _possibly true_.

This is what #fltl4 provides. It keeps the operators of FLTL and its complementation, and changes
one thing only: instead of two truth values it uses four, the domain $bb(B)_4$. Each of $top$ and
$bot$ is split in two, a definitive verdict and a presumable one, so that a monitor can answer
_true (or false) for now_ while leaving room for the rest of the run.


#figure(
  placement: top,
  diagram(
    spacing: (3.4em, 2.1em),
    node-outset: 0pt,

    // ── an observed run of φ ≡ G(r → F a) ───────────────────
    tdot((0, 0), name: <f0>),
    tdot((1, 0), name: <f1>),
    tdot((2, 0), name: <f2>),
    edge(<f0>, <f1>, stroke: cgray + 1pt),
    edge(<f1>, <f2>, stroke: cgray + 1pt),
    node((0, -.55), dtext(size: .82em, $r$)),
    node((1, -.55), dtext(size: .82em, $a$)),
    node((2, -.55), dtext(size: .82em, $r$)),

    // ── the verdict FLTL emits after each event ─────────────
    node((-1, .55), dtext(fill: caxis, size: .74em)[FLTL verdict]),
    node((0, .55), text(fill: credD, size: .95em, $bot$)),
    node((1, .55), text(fill: ctealD, size: .95em, $top$)),
    node((2, .55), text(fill: credD, size: .95em, $bot$)),

    // ── two continuations of the same prefix ────────────────
    vpill((4, -.9), $top$, cteal, [request served], name: <fu>),
    vpill((4, .9), $bot$, cred, [never served], name: <fd>),
    edge(
      <f2>,
      <fu>,
      "-->",
      elbl($dots a dots$, caxis),
      label-side: left,
      stroke: (paint: caxis, dash: "dashed", thickness: .8pt),
    ),
    edge(
      <f2>,
      <fd>,
      "-->",
      elbl($r^ω$, caxis),
      label-side: right,
      stroke: (paint: caxis, dash: "dashed", thickness: .8pt),
    ),
  ),
  caption: [
    $φ ≡ bold(G) (r -> bold(F) a)$ on a run that keeps requesting. The two continuations of the same prefix disagree, so no final verdict is warranted.
  ],
) <fig-futures>

== Maxims for Runtime Verification

The four maxims below say precisely what we expect from such a semantics.

+ *Existential next.* Saying "$φ$ holds at the next step" presupposes that a next
  step exists — and on a finite trace we may have run out of events. The
  logic therefore needs a _strong_ next $bold(X)$, which refuses to hold when the
  trace stops here, alongside the _weak_ next $overline(bold(X))$, which accepts
  it.

+ *Complementation by negation.* Negating a formula must really flip its verdict:
  $not φ$ evaluates to the complement of $φ$'s verdict, and that complement is
  always a _different_ value. No verdict may be its own complement — which is why
  a single "don't know" value will not do, and why the presumable verdicts come in the pair `potentially` $⊤$ / `potentially` $⊥$.

+ *Impartiality.* A monitor must not jump to conclusions. As long as some
  infinite continuation of what we have seen so far would lead to a different
  answer, the trace must not be given a final $⊤$ or $⊥$; the most it may say is
  "true (false) so far".

+ *Anticipation.* Conversely, a monitor must not sit on a conclusion it can
  already draw. The moment every infinite continuation agrees on one verdict, the
  finite trace must already be evaluated to that verdict.

== Syntax and Semantics


#let b4-def = $ bb(B)_4 = { top, top^p, bot^p, bot } $
#let b4-order = $ bot subset.sq bot^p subset.sq top^p subset.sq top $

#let b4-compl = $
  overline(top) = bot quad overline(top^p) = bot^p quad overline(bot^p) = top^p quad overline(bot) = top
$

#definition([Truth domain $bb(B)_4$], label: <def:b4>)[
  The truth domain of #fltl4 is the four valued set
  #b4-def
  where $top$ (resp. $bot$) denotes the definitive verdict _true_ (resp. _false_) and
  $top^p$ (resp. $bot^p$) the presumable verdict _presumably true_ (resp.
  _presumably false_). It is a finite distributive de Morgan lattice
  $(bb(B)_4, subset.sq.eq)$, hence a truth domain in the sense of @def:truth-dom[-], along the order:
  #b4-order
  with $inter.sq$ and $union.sq$ the meet and join of that order, and with
  complementation defined as:
  #b4-compl
]

#let b4-not-boolean-top = $top^p union.sq overline(top^p) = top^p union.sq bot^p = top^p != top$
#let b4-not-boolean-bot = $bot^p inter.sq overline(bot^p) = bot^p != bot$

#proposition()[
  The $bb(B)_4$ is _not_ a Boolean lattice: the presumable verdicts satisfy
  #b4-not-boolean-top, and dually
  #b4-not-boolean-bot. This is precisely what lets a monitor
  report a verdict that is not yet final.
]

#let fltl4-syntax = $
  φ, ψ ::= "true" | "false" | p | ¬ φ | φ and ψ | φ or ψ | bold(X) φ | overline(bold(X)) φ
  | φ until ψ | φ release ψ | bold(F) φ | bold(G) φ
$

#definition([Syntax of #fltl4 formulae], label: <def:fltl4-syntax>)[
  Let $Σ = 2^bold("AP")$ be the finite alphabet built over a finite set of atomic
  propositions $bold("AP")$, with $p ∈ bold("AP")$ an atomic proposition and
  $a ∈ Σ$ a letter. The set of #fltl4 formulae is inductively defined by the following
  grammar:
  #fltl4-syntax
  In contrast to LTL (@def:ltl-syntax[-]), the constants range over the whole of
  $bb(B)_4$, which is often considered in the context of multi-valued logics , and $bold(F)$ and $bold(G)$ are taken as primitive operators rather than
  as abbreviations.
]

#let fltl4-sem = align(center)[
  #grid(
    columns: (auto, auto),
    column-gutter: 2.2em,
    row-gutter: 1.4em,
    align: left,
    [
      #fgrp[Boolean constants]
      $
         sem(w tack.rr "true") & = top \
        sem(w tack.rr "false") & = bot
      $
    ],
    [
      #fgrp[Boolean combinations]
      $
             sem(w tack.rr ¬φ) & = overline(sem(w tack.rr φ)) \
         sem(w tack.rr φ or ψ) & = sem(w tack.rr φ) union.sq sem(w tack.rr ψ) \
        sem(w tack.rr φ and ψ) & = sem(w tack.rr φ) inter.sq sem(w tack.rr ψ)
      $
    ],

    [
      #fgrp[atomic propositions]
      $
         sem(w tack.rr p) & = cases(
                              top & "if " p in w_1,
                              bot & "if " p in.not w_1
                            ) \
        sem(w tack.rr ¬p) & = cases(
                              top & "if " p in.not w_1,
                              bot & "if " p in w_1
                            )
      $
    ],
    [
      #fgrp[(weak) next]
      $
                  sem(w tack.rr bold(X) φ) & = cases(
                                               sem(w^2 tack.rr φ) & "if " abs(w) > 1,
                                               text(fill: cteal, bot^p) & "else"
                                             ) \
        sem(w tack.rr overline(bold(X)) φ) & = cases(
                                               sem(w^2 tack.rr φ) & "if " abs(w) > 1,
                                               text(fill: cteal, top^p) & "else"
                                             )
      $
    ],
  )

  #block(width: 100%)[
    #align(left, fgrp[until/release])
    $
      sem(w tack.rr φ until ψ) & = union.sq.big_(1 <= i <= abs(w)) (
                                       sem(w^i tack.rr ψ) inter.sq inter.sq.big_(1 <= j < i) sem(w^j tack.rr φ)
                                     )
                                     union.sq (
                                       text(fill: cteal, bot^p) inter.sq inter.sq.big_(1 <= i <= abs(w)) sem(w^i tack.rr φ)
                                     ) \
                                   \
      sem(w tack.rr φ release ψ) & = inter.sq.big_(1 <= i <= abs(w)) (
                                       sem(w^i tack.rr ψ) union.sq union.sq.big_(1 <= j < i) sem(w^j tack.rr φ)
                                     )
                                     inter.sq (
                                       text(fill: cteal, top^p) union.sq union.sq.big_(1 <= i <= abs(w)) sem(w^i tack.rr φ)
                                     )
    $

    #align(left, fgrp[finally/globally])
    $
      sem(w tack.rr bold(F) φ) & = text(fill: cteal, bot^p) union.sq union.sq.big_(1 <= i <= abs(w)) sem(w^i tack.rr φ) \
      sem(w tack.rr bold(G) φ) & = text(fill: cteal, top^p) inter.sq inter.sq.big_(1 <= i <= abs(w)) sem(w^i tack.rr φ)
    $
  ]
]

#figure(
  placement: top,
  fltl4-sem,
  caption: [Semantics of #fltl4 formulae over a non-empty finite trace $w = w_1 dots w_(abs(w)) ∈ Σ^+$],
) <fig-fltl4-sem>

#todo(position: "inline")[Semantics equivalence between F, G and U, R ??]


#let fltl4-sem-sig = $
  sem(- tack.rr -) : Σ^+ × #fltl4 -> bb(B)_4
$

#definition([Semantics of #fltl4], label: <def:fltl4-sem>)[
  The truth value of an #fltl4 formula $φ$, denoted with $sem(w tack.rr φ)$, is given by the function
  #fltl4-sem-sig
  which is defined inductively as shown in @fig-fltl4-sem.
]

Where FLTL falls back on $bot$ and $top$ when the trace runs out (@fig-fltl4-sem, cases
$abs(w) = 1$ for the next operators, and the second disjunct of until/release), #fltl4
falls back on the presumable verdicts $bot^p$ and $top^p$ instead. A definitive verdict
is therefore emitted only when the observed prefix alone already settles the formula,
which is what impartiality asks for.

== Monitor as a Mealy machine

A _state machine_ is a procedure that consumes the input letter by letter and outputs the semantics of the trace read so far with respect to the formula the monitor was built for.
For each temporal formula registered to the `monitor` it is then compiled into a Mealy machine, also called #acr("FSM").

#let mealy-tuple = $cal(M) = (S, s_0, Σ, Γ, δ)$
#let mealy-delta = $delta : Sigma times S -> Gamma times S$

#definition("Mealy machine", label: <def:mealy>)[
  A Mealy machine is a tuple  #mealy-tuple:
  - $S$ a finite set of states,
  - a start state $s_0 ∈ S$,
  - Σ is a finite set called the input alphabet,
  - Γ is the output alphabet and,
  - #mealy-delta is the transition function.
]

we are now ready to define the monitor  #acr("FSM") #M4 computing the #fltl4 semantics in @def:fltl4-sem[-].

#let m4-tuple = $cal(M)_4^phi = (S, s_0, Σ, bb(B)_4, delta_4)$

#let m4-delta = grid(
  columns: (1fr, 1fr),
  column-gutter: 1.5em,
  $
         delta_4 (a, "true") & = (top, "true") \
        delta_4 (a, "false") & = (bot, "false") \
              delta_4 (a, p) & = cases(
                                 (top, "true") & "if " p in a,
                                 (bot, "false") & "else"
                               ) \
          delta_4 (a, not p) & = cases(
                                 (bot, "false") & "if " p in a,
                                 (top, "true") & "else"
                               ) \
     delta_4 (a, phi or psi) & = (v_phi union.sq v_psi, "nrm" (phi' or psi')) \
    delta_4 (a, phi and psi) & = (v_phi inter.sq v_psi, "nrm" (phi' and psi'))
  $,
  $
              delta_4 (a, X phi) & = (bot^p, phi) \
    delta_4 (a, overline(X) phi) & = (top^p, phi) \
          delta_4 (a, phi U psi) & = delta_4 (a, psi or (phi and X (phi U psi))) \
          delta_4 (a, phi R psi) & = delta_4 (a, psi and (phi or overline(X) (phi R psi))) \
              delta_4 (a, F phi) & = delta_4 (a, phi or X F phi) \
              delta_4 (a, G phi) & = delta_4 (a, phi and overline(X) G phi)
  $,
)

#definition([#acr("FSM") #M4], label: <def:m4>)[
  A `monitor` for #fltl4 is defined by the tuple #m4-tuple with the following transition function:

  #m4-delta
  where _nrm_ is a normalisation function, let unspecified yet, of a formula $phi$ that eliminate any redundancy present in the formula.
]

#example("Mealy construction", label: <ex:m4-req-ack>)[
  Take the request/acknowledge property of @fig-futures over $bold("AP") = {r, a}$, with the
  two-letter alphabet $Σ = {r, a}$ writing $r := {r}$ for a request and $a := {a}$ for an
  acknowledgement. Reading $r -> bold(F) a$ as $¬ r or bold(F) a$, @def:m4[-] unfolds
  $bold(G)(r -> bold(F) a) = (¬ r or bold(F) a) and overline(bold(X)) bold(G)(r -> bold(F) a)$,
  and yields the four transitions
  $
                  delta_4(a, bold(G)(r -> bold(F) a)) & = (top^p, bold(G)(r -> bold(F) a)) \
                  delta_4(r, bold(G)(r -> bold(F) a)) & = (bot^p, bold(F) a and bold(G)(r -> bold(F) a)) \
    delta_4(a, bold(F) a and bold(G)(r -> bold(F) a)) & = (top^p, bold(G)(r -> bold(F) a)) \
    delta_4(r, bold(F) a and bold(G)(r -> bold(F) a)) & = (bot^p, bold(F) a and bold(G)(r -> bold(F) a))
  $
  The pending $bold(F) a$ is the memory of a request awaiting its acknowledgement, and $"nrm"$
  closes the state space by collapsing a second request onto that same obligation. The $top^p$
  of each output and the $bold(G)(r -> bold(F) a)$ carried into each successor both come from
  the $overline(bold(X)) bold(G)(r -> bold(F) a)$ of the unfolding, which is why the globally
  never expires and never commits.

  #v(.3em)
  #align(center, diagram(
    spacing: (7.6em, 2.4em),
    node-outset: 2pt,
    sbox((0, 0), $bold(G)(r -> bold(F) a)$, cteal, name: <q0>),
    sbox((1, 0), $bold(F) a and bold(G)(r -> bold(F) a)$, cpurpD, name: <q1>),
    edge(<q0>, <q1>, "->", elbl($r | bot^p$, credD), bend: 32deg, stroke: cgray + .7pt),
    edge(<q1>, <q0>, "->", elbl($a | top^p$, ctealD), bend: 32deg, stroke: cgray + .7pt),
    edge(<q0>, <q0>, "->", elbl($a | top^p$, ctealD), bend: 130deg, stroke: cgray + .7pt),
    edge(<q1>, <q1>, "->", elbl($r | bot^p$, credD), bend: -130deg, stroke: cgray + .7pt),
  ))
  #v(.3em)

  No state emits $top$ or $bot$: no finite prefix settles this property, and the machine only
  ever reports _presumably_ true or false, as impartiality demands.
]

Following the characterization of #fltl4, we can etablish a correspondance between #fltl4 semantics and #acr("FSM") $cal(M)$.

#let m4-run = $
  delta_4^* (ϵ, phi) = (v_ϵ, phi) quad quad
  delta_4^* (a, phi) = delta_4 (a, phi) quad quad
  delta_4^* (a rho, phi) = delta_4^* (rho, delta_4 (a, phi)_s)
$

#definition([Run of #M4], label: <def:m4-run>)[
  Write $(-)_o$ and $(-)_s$ for the projections of $bb(B)_4 times S$ on the output and on the
  state. The _run_ of #M4 is the map $delta_4^* : Σ^* times S -> bb(B)_4 times S$ defined by
  induction on the word, for $a ∈ Σ$ and $rho ∈ Σ^+$:
  #m4-run
  so $delta_4^* (rho, phi)_o$ is the verdict emitted on the last letter of $rho$, and
  $delta_4^* (rho, phi)_s$ the residual reached after it.
]

#todo(position: "inline")[Fix the verdict $v_ϵ$ emitted on the empty trace, together with $sem(ϵ tack.rr phi)$.]

#let m4-correct = $
  delta_4^* (rho, phi)_o = sem(rho tack.rr phi)
$

// the justification of a step in a chain of equalities
#let why = body => text(size: .85em, fill: cgray)[(#body)]

// a case of an induction, boxed
#let icase = body => box(
  stroke: .6pt + caxis,
  inset: (x: .4em, y: .25em),
  outset: (y: .1em),
  radius: 2pt,
  body,
)

#theorem([Correctness of #M4], label: <thm:m4-correct>)[
  Let $phi$ be an #fltl4 formula in negation normal form. Then there is an effective procedure constructing an FSM #m4-tuple with $s_0 = phi$ such that for all $rho ∈ Σ^*$ the following holds:
  #m4-correct
]
#proof[
By induction on $rho$.
- #icase($rho = ϵ$) We have to show that $forall phi. #h(.2em) delta_4^* (ϵ, phi)_o = sem(ϵ tack.rr phi)$, that is $v_ϵ = sem(ϵ tack.rr phi)$ by @def:m4-run[-].
- #icase($rho = a rho'$) #h(.4em) IH on $rho'$: $forall psi. #h(.2em) delta_4^* (rho', psi)_o = sem(rho' tack.rr psi)$. \ We have to prove that $forall phi. #h(.2em) delta_4^* (a rho', phi)_o = sem(a rho' tack.rr phi)$. \ We proceed by induction on $phi$:
  
- #icase($phi = "true"$) #h(.4em) We need to check that $delta_4^* (a rho', "true")_o = sem(a rho' tack.rr "true")$.
  
- #icase($phi = "false"$) #h(.4em) The task is to prove that $delta_4^* (a rho', "false")_o = sem(a rho' tack.rr "false")$.
  
- #icase($phi = p$) #h(.4em) We want to show that $delta_4^* (a rho', p)_o = sem(a rho' tack.rr p)$.
  
- #icase($phi = ¬ p$) #h(.4em) One must prove that $delta_4^* (a rho', ¬ p)_o = sem(a rho' tack.rr ¬ p)$.
  
- #icase($phi = psi_1 or psi_2$) #h(.4em) IH on $psi_1, psi_2$: $delta_4^* (a rho', psi_i)_o = sem(a rho' tack.rr psi_i)$ for $i = 1, 2$. \ We are to show that $delta_4^* (a rho', psi_1 or psi_2)_o = sem(a rho' tack.rr psi_1 or psi_2)$.
  
- #icase($phi = psi_1 and psi_2$) #h(.4em) IH on $psi_1, psi_2$: $delta_4^* (a rho', psi_i)_o = sem(a rho' tack.rr psi_i)$ for $i = 1, 2$. \ The obligation is $delta_4^* (a rho', psi_1 and psi_2)_o = sem(a rho' tack.rr psi_1 and psi_2)$.
  
- #icase($phi = bold(X) psi$) #h(.4em) IH on $psi$: $delta_4^* (a rho', psi)_o = sem(a rho' tack.rr psi)$. \ We need to show that $delta_4^* (a rho', bold(X) psi)_o = sem(a rho' tack.rr bold(X) psi)$.
  
- #icase($phi = overline(bold(X)) psi$) #h(.4em) IH on $psi$: $delta_4^* (a rho', psi)_o = sem(a rho' tack.rr psi)$. \ The statement to prove is $delta_4^* (a rho', overline(bold(X)) psi)_o = sem(a rho' tack.rr overline(bold(X)) psi)$.
  
- #icase($phi = psi_1 until psi_2$) #h(.4em) IH on $psi_1, psi_2$: $delta_4^* (a rho', psi_i)_o = sem(a rho' tack.rr psi_i)$ for $i = 1, 2$. \ We must show that $delta_4^* (a rho', psi_1 until psi_2)_o = sem(a rho' tack.rr psi_1 until psi_2)$.
  
- #icase($phi = psi_1 release psi_2$) #h(.4em) IH on $psi_1, psi_2$: $delta_4^* (a rho', psi_i)_o = sem(a rho' tack.rr psi_i)$ for $i = 1, 2$. \ This time the goal is $delta_4^* (a rho', psi_1 release psi_2)_o = sem(a rho' tack.rr psi_1 release psi_2)$.
  
- #icase($phi = bold(F) psi$) #h(.4em) IH on $psi$: $delta_4^* (a rho', psi)_o = sem(a rho' tack.rr psi)$. \ Here the claim is $delta_4^* (a rho', bold(F) psi)_o = sem(a rho' tack.rr bold(F) psi)$.
  
- #icase($phi = bold(G) psi$) #h(.4em) IH on $psi$: $delta_4^* (a rho', psi)_o = sem(a rho' tack.rr psi)$. \ Finally, we have to show that $delta_4^* (a rho', bold(G) psi)_o = sem(a rho' tack.rr bold(G) psi)$.
]