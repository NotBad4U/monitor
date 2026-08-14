#import "@preview/mmdr:0.2.2": mermaid
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/codly:1.3.0"
#import "@preview/acrostiche:0.7.0": *
#import "@preview/theoretic:0.4.0"
#import "@preview/xarrow:0.4.0": xarrow, xarrowSquiggly, xarrowTwoHead
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set

#import theoretic.presets.basic: * // this will automatically load predefined styled environments
#show ref: theoretic.show-ref      // this is necessary for references to theorems to work

#import "@preview/cetz:0.5.2"
#show ref: theoretic.show-ref      // this is necessary for references to theorems to work



// a Mealy machine drawn as a box
#let mbox = (pos, lbl, ..args) => node(pos, lbl, shape: fletcher.shapes.rect, stroke: .6pt, inset: 9pt, ..args)
#let compbox = (enc, inset: 16pt, ..args) => node(
  enclose: enc,
  stroke: (paint: gray, dash: "dashed", thickness: .6pt),
  inset: inset,
  ..args,
)

#let fltl4 = `FLTL₄`
#let M4 = $cal(M)_4^phi$

#set document(title: [Reactor: a #fltl4 monitor])


#show heading.where(level: 1): set heading(numbering: "1")


#set page(
  numbering: "1",
  number-align: center + bottom, // Places number in the header
)

#set par(justify: true, first-line-indent: 1.5em)

#init-acronyms((
  "RV": ("Runtime Verification", "Runtime Verifications"),
  "FSM": ("Finite State Machine", "Finite State Machines"),
))

#title()

// ---------- palette ----------
#let cteal = rgb("#1D9E75")
#let ctealD = rgb("#0F6E56")
#let camber = rgb("#EF9F27")
#let camberD = rgb("#B26E0A")
#let cred = rgb("#E24B4A")
#let credD = rgb("#A32D2D")
#let cpurp = rgb("#7F77DD")
#let cpurpD = rgb("#534AB7")
#let cgray = rgb("#5F5E5A")
#let caxis = rgb("#888780")
// ---------- end palette ----------

// ---------- diagram kit ----------
#let dfont = ("Avenir Next", "Helvetica Neue")

#let dtext(fill: cgray, size: .85em, weight: "medium", body) = text(
  font: dfont,
  size: size,
  fill: fill,
  weight: weight,
  body,
)

// a soft, rounded, tinted node
#let sbox = (pos, body, hue, ..args) => node(
  pos,
  body,
  shape: fletcher.shapes.rect,
  fill: hue.lighten(88%),
  stroke: hue.darken(12%) + .9pt,
  corner-radius: 6pt,
  inset: 10pt,
  ..args,
)

// an edge label
#let elbl = (body, col) => dtext(fill: col, size: .78em, body)

// one truth value of B₄: a mark (polarity) over its symbol; hue = certainty,
// full size = definitive verdict, smaller = presumable one
#let vmark = (mark, col, lbl, size: 1.15em) => stack(
  dir: ttb,
  spacing: .32em,
  text(fill: col, size: size, mark),
  text(font: dfont, size: .62em, fill: col.darken(8%), lbl),
)
// an observed event on a trace timeline
#let tdot = (pos, ..args) => node(pos, none, shape: circle, radius: 3.2pt, fill: cgray, stroke: none, ..args)

// a state that has not been observed (beyond the end of the trace)
#let gdot = (pos, ..args) => node(
  pos,
  none,
  shape: circle,
  radius: 3.2pt,
  fill: white,
  stroke: caxis + .8pt,
  ..args,
)

// a verdict reached by one possible continuation, with a gloss
#let vpill = (pos, sym, hue, note, ..args) => node(
  pos,
  stack(
    dir: ltr,
    spacing: .6em,
    text(fill: hue.darken(12%), size: 1em, sym),
    dtext(fill: caxis, size: .72em, note),
  ),
  fill: hue.lighten(92%),
  stroke: hue.darken(12%) + .8pt,
  corner-radius: 5pt,
  inset: 7pt,
  ..args,
)
// ---------- end diagram kit ----------

#let sem2(x) = $lr(⟦ #x ⟧)_2$ // semantic bracket  ⟦ … ⟧_2
#let sem(x) = $lr(⟦ #x ⟧)_4$ // semantic bracket  ⟦ … ⟧₄
#let semw(x) = $lr(⟦ #x ⟧)_ω$ // semantic bracket ⟦ … ⟧_ω : LTL over infinite traces
#let semf(x) = $lr(⟦ #x ⟧)_F$ // semantic bracket ⟦ … ⟧_F : FLTL over finite traces

// ---------- profunctor / arrow notation ----------
#let Mly = $bold("Mly")$ // the category of Mealy behaviours
#let seq = $thin class("binary", #text(size: 1em, baseline: .1em)[⨟]) thin$ // series composition
#let fan(m, n) = $lr(⟨ #m, #n ⟩)$ // fan-out: one input, paired outputs
#let tr(a, b) = $xarrow(sym: -->, #a|#b)$ // s --a|b--> s′
#let beh = $mu$ // the behaviour map into the final coalgebra
#let Fre = $"Free"_(frak(M))$ // the free monad of the Mealy functor: plans
// ---------- end profunctor notation ----------

// the small bold rubric heading a group of equations inside a semantics figure
#let fgrp = body => text(weight: "bold", size: .95em, body)

// a `cases` branch whose verdict is held vertically centred against a
// multi-line side condition
#let mcase = (verdict, ..rows) => box(grid(
  columns: (auto, auto),
  column-gutter: .6em,
  align: (horizon, left + horizon),
  verdict, grid(columns: 1, row-gutter: .75em, align: left, ..rows.pos()),
))

// the matching single-line branch, indented to line up with `mcase`
#let scase = (verdict, body) => box(grid(
  columns: (auto, auto),
  column-gutter: .6em,
  align: left,
  verdict, body,
))



= Context

#acr("RV") @Bartocci2018IntroductionTR is a lightweight (yet rigorous) method that complements classical exhaustive verification techniques (such as model checking and theorem proving) with a more practical approach and try to be closer to the actual real system.
RV works by analyzing the trace of the system's actual execution, comparing it against a formal specification of the system behavior.
This task is perform by a _monitor_ (cf. @fig-rv-loop) that run alongside a system to observe its behavior and determine if it satisfies a specified correctness property.
The main advantage using RV can give precise information on the runtime behavior of the monitored system, without the pitfalls of developing models that require a re-implementation of the entire system in a modeling language.

Monitors can be classified as _offline_ and _online_ monitors @taxonomy-rv.
Offline monitor @tla-rv process the traces generated by a system after the events, generally by reading the trace execution from a permanent storage system.
Online monitors process the trace during the execution of the system. Online monitors are said to be synchronous if the processing of an event is attached to the system execution, blocking the system during the event monitoring.
On the other hand, an asynchronous monitor has its execution detached from the system.
Each type of monitor has a set of advantages. For example, offline monitors can be executed on different machines but require operations to save the log to a file.
In contrast, synchronous online method can react at the exact moment a violation occurs.

This document aims to specify the development of Reactor -- a online monitor to verify if program guarantee some
temporal assertions defined in the Finite Temporal Linear Logic 4 (FLTL4) @rv-ltl@ltl-book, a suitable temporal logic for RV @rv-ltl.
A `monitor` is created from a  FLTL4 `property`. The monitor is an Mealy machine equivalent to the property.
This is possible because all FLTL4 formulas can be transformed into a Mealy machine @rv-ltl.


#figure(
  placement: bottom,
  diagram(
    spacing: (5.2em, 4.2em),
    node-outset: 2pt,

    // ── property ──────────────────────────────────────────────
    node(
      (0, 0),
      stack(
        dir: ttb,
        spacing: 1em,
        dtext(fill: cpurpD, weight: "bold")[property],
        text(size: .9em, fill: cpurpD, $tack.rr space square (A -> diamond B)$),
      ),
      shape: fletcher.shapes.ellipse,
      fill: cpurp.lighten(90%),
      stroke: cpurpD + .9pt,
      inset: 12pt,
      name: <prop>,
    ),

    // ── monitor ───────────────────────────────────────────────
    sbox((0, 1), dtext(fill: ctealD, weight: "bold")[monitor], cteal, name: <mon>),

    // ── verdict ───────────────────────────────────────────────
    node(
      (1.15, 1),
      stack(
        dir: ltr,
        spacing: .7em,
        emoji.checkmark,
        "|",
        emoji.crossmark,
      ),
      fill: white,
      stroke: cgray + .9pt,
      corner-radius: 6pt,
      inset: 9pt,
      name: <verd>,
    ),

    // ── instrumentation ∙ system ──────────────────────────────
    sbox(
      (0, 2.15),
      stack(
        dir: ttb,
        spacing: .45em,
        text(size: 1.45em, emoji.gear),
        dtext(fill: cgray.darken(20%), weight: "bold")[System],
      ),
      cgray,
      name: <sys>,
    ),
    node((0, 2.62), dtext(fill: caxis, size: .74em)[Instrumentation], name: <ilbl>),
    node(
      enclose: (<sys>, <ilbl>),
      inset: 12pt,
      stroke: (paint: caxis, dash: "dashed", thickness: .7pt),
      corner-radius: 8pt,
      name: <instr>,
    ),

    // ── wiring ────────────────────────────────────────────────
    edge(<prop>, <mon>, "->", stroke: cpurpD + .7pt),
    edge(<mon>, <instr>, "->", elbl([Feedback], caxis), shift: 9pt, label-side: left, stroke: caxis + .7pt),
    edge(<instr>, <mon>, "->", elbl([Observe], caxis), shift: 9pt, label-side: left, stroke: caxis + .7pt),
    edge(<mon>, <verd>, "->", elbl([Verdict], caxis), label-side: left, stroke: caxis + .7pt),
  ),
  caption: [The runtime-verification loop],
) <fig-rv-loop>

== Overview

The rest of this document is organised as follows:
- @sec-prelim fixes the notation used throughout.
- @sec-fltl4 presents the #fltl4 logic: the maxims a semantics for runtime verification must
respect, the syntax of #fltl4 over the four-valued domain $bb(B)_4$, its semantics,
and the Mealy machine a formula is compiled into.
- @sec-dev describes the implementation of the `monitor` built from these machines.

= Preliminaries <sec-prelim>

== Traces

For the remainder of this article, let $bold("AP")$ be a finite and non-empty set of atomic propositions and
$Σ=2^bold("AP")$ a finite alphabet. We write $a_i$ for any single element of $Σ$, i.e. $a_i$ is a possibly empty subset
of propositions taken from AP. Finite traces over $Σ$ are elements of $Sigma^∗$, usually denoted with $u,u',u_1,u_2, dots$. The empty trace is denoted with ϵ. Infinite traces are elements of $Σ^ω$, usually denoted with $w, w', w_1, w_2, dots$ For some infinite trace $w = a_0a_1 ...$, we denote with $w^i$ the suffix $a_i, a_(i+1) dots$ . In case of a finite trace $u=a_0a_1 ...a_(n−1)$, $u^i$ denotes the suffix $a_i a_(i+1) ...a_(n−1)$ for $0 ≤ i < n$ and the empty string ϵ for $n ≤ i$.

== Truth domain

A lattice is a partially ordered set $(cal(L), ⊑)$ where for each $x,y ∈ cal(L)$, there exists (i) a unique greatest
lower bound (glb), which is called the meet of $x$ and $y$, and is denoted with $x ⊓ y$, and (ii) a unique
least upper bound (lub), which is called the join of $x$ and $y$, and is denoted with $x ⊔ y$. A lattice is called
finite iff $L$ is finite. Every finite lattice has a well-defined unique least element, called bottom, denoted
with $⊥$, and analogously a greatest element, called top, denoted with . A lattice is distributive, iff $x ⊓
(y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)$, and, dually, $x ⊔ (y ⊓ z)=(x ⊔ y) ⊓ (x ⊔ z)$. In a _de Morgan_ lattice, every element
$x$ has a unique dual element $overline(x)$, such that $overline(overline(x)) = x$ and $x ⊑ y$ implies $overline(y) ⊑ overline(x)$. A distributive lattice is called Boolean iff $x ⊔ overline(x) = ⊤$ and $x ⊓ overline(x) = ⊥$.
As the common denominator of the semantics for the subsequently defined logics is a finite de Morgan lattice, we take this to our understanding of a truth domain.

We consider the traditional two-valued semantics that we denotes $bb(B)_2$ with truth values `true`, denoted with $top$, and `false`, denoted with $bot$. Truth values should be comparable and combinable in terms of Boolean operations expressed by the connectives of the underlying logic, we interpret these truth values as elements of a _de Morgan_ lattice.

#definition("Truth domain", label: <def:truth-dom>)[
  We call $cal(D)$ a _truth domain_, if it is a finite de Morgan lattice. The two valued truth domain $bb(B)_2 = { top, bot}$ is a Boolean lattice with $bot subset.sq top$ and $inter.sq$ and $union.sq$ definedin the expected manner.
]

== LTL and FLTL

we first recall LTL interpreted over infinite traces, as introduced by Pnueli @ltl in the setting of specification and verification.
In case of LTL over infinite traces, one is used to have a syntax ranging over a small set of temporal and Boolean operators and to add additional operators by means of abbreviations.
The set of LTL formulae is defined using _true_, the atomic propositions $p ∈ bold("AP")$, disjunction, _next_ *X* and _until_ *U*, as positive operators, together with _negation_ ¬.
For comparison with logics over finite traces, we moreover add dual operators, namely false, $¬p$, weak next $overline(X)$ and release *R*, respectively.

#definition("Syntax of LTL formulae", label: <def:ltl-syntax>)[
  Let $p$ be an atomic proposition from a finite set of atomic propositions $bold("AP")$. The set of
  LTL formulae, denoted with LTL, is inductively defined by the following grammar:
  $
    φ & ::= "true" | p | φ or φ | φ bold("U") φ | bold(X) φ \
    φ & ::= "false" | ¬p | φ and φ | φ bold("R") φ | overline(bold(X)) φ \
    φ & ::= ¬φ
  $
]

Moreover, we define by means of abbreviation the _finally_ $bold(F)$ and _globally_ $bold(G)$
operators as

$ bold(F) φ := "true" bold("U") φ quad "and" quad bold(G) φ := ¬ bold(F) ¬φ $

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
        semw(w tack.rr φ bold("U") ψ) & = cases(
                                          gap: #.7em,
                                          #mcase(
                                            $top$,
                                            $"there is a " k >= 0 : semw(w^k tack.rr ψ) = top " and"$,
                                            $"for all " l " with " 0 <= l < k : semw(w^l tack.rr φ) = top$,
                                          ),
                                          #scase($bot$, $"else"$),
                                        ) \
                                      \
        semw(w tack.rr φ bold("R") ψ) & = cases(
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

Inspecting the semantics, we observe that there is no difference of $bold(X)$ and
$overline(bold(X))$ in LTL over infinite traces. However, $overline(bold(X))$ acts differently
when finite traces are considered.

FLTL @rv-ltl is the interpretation of that same syntax (@def:ltl-syntax[-]) over a _finite_ trace,
still in $bb(B)_2$. Its semantics function is constructed like the one for standard LTL but with
two modifications: if a strong next-state operator in some subformula $bold(X) φ$ is referring to
a state beyond the known finite prefix $u$, then this subformula is evaluated to $bot$, regardless
of $φ$. Likewise, a subformula $overline(bold(X)) φ$ always evaluates to $top$ if it refers to a
state beyond $u$. This approach is extended to the definition of the until and release operators.
For example, to satisfy $φ bold("U") ψ$ with a finite trace $u$, there must exist a position
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
        semf(u tack.rr φ bold("U") ψ) & = cases(
                                          gap: #.7em,
                                          #mcase(
                                            $top$,
                                            $"there is a " k ∈ {0, dots n-1} : semf(u^k tack.rr ψ) = top " and"$,
                                            $"for all " l " with " 0 <= l < k : semf(u^l tack.rr φ) = top$,
                                          ),
                                          #scase($bot$, $"else"$),
                                        ) \
                                      \
        semf(u tack.rr φ bold("R") ψ) & = cases(
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



= The logic #fltl4 <sec-fltl4>

FLTL interprets LTL formulae over finite traces.
That is the right reading for a _completed_ run of the execution of a program that terminated and that
no more new event are expected. However, it is a wrong approach for runtime verification, where the trace
in hand is a _prefix_ of a run still being produced i.e. the next event has not arrived yet.
Two failures follow:
- the strong next $bold(X) phi$ has to infer;
- and a two-valued verdict can never be provisional.

The second aspect that expose that with only $top$ and $bot$ available, every verdict is final.
A two-valued semantics has to commit after each event even when the run could still go either way.
Take the request/acknowledge property $φ ≡ bold(G) (r -> bold(F) a)$ of @fig-futures. If the prefix
ends on a request $r$, FLTL evaluates $phi$ to $bot$, but it is too early to say that. $bot$ reads as
_the property is violated_, whereas here we are simply still waiting for the acknowledgement $a$,
which may well arrive later. The honest answer is not a definitive false but something weaker:
_false so far_, or _possibly true_.

This is what #fltl4 provides. It keeps the operators of FLTL and its complementation, and changes
one thing only: instead of two truth values it uses four, the domain $bb(B)_4$. Each of $top$ and
$bot$ is split in two, a definitive verdict and a presumable one, so that a monitor can answer
_true (or false) for now_ while leaving room for the rest of the run. The four maxims below say
precisely what we expect from such a semantics.

#figure(
  placement: top,
  stack(
    dir: ttb,
    spacing: 1.4em,
    diagram(
      spacing: (3.2em, 2em),
      node-outset: 0pt,

      // ── the observed prefix u ──────────────────────────────
      tdot((0, 0), name: <h0>),
      tdot((1, 0), name: <h1>),
      tdot((2, 0), name: <h2>),
      edge(<h0>, <h1>, stroke: cgray + 1pt),
      edge(<h1>, <h2>, stroke: cgray + 1pt),
      node((0, .5), dtext(size: .8em, $a_0$)),
      node((1, .5), dtext(size: .8em, $a_1$)),
      node((2, .5), dtext(size: .8em, $a_(n-1)$)),
      node((1, -.95), dtext(size: .78em)[observed prefix $u$]),

      // ── everything past the last letter ────────────────────
      gdot((3, 0), name: <h3>),
      gdot((4, 0), name: <h4>),
      edge(<h2>, <h3>, stroke: (paint: caxis, dash: "dashed", thickness: .8pt)),
      edge(<h3>, <h4>, stroke: (paint: caxis, dash: "dashed", thickness: .8pt)),
      node((3, .5), dtext(fill: caxis, size: .8em, $a_n$)),
      node((4, .5), dtext(fill: caxis, size: .8em, $dots$)),
      node((3.6, -.95), dtext(fill: caxis, size: .78em)[not observed yet]),

      // ── the horizon the strong next falls over ─────────────
      edge((2.5, -1.25), (2.5, .85), stroke: (paint: credD, dash: "densely-dotted", thickness: 1pt)),
      node((2.5, 1.25), dtext(fill: credD, size: .74em)[end of trace]),
    ),
    $
      semf(u tack.rr bold(X) φ) = bot quad "and" quad semf(u tack.rr overline(bold(X)) φ) = top
      quad "for every " φ, "whenever " u^1 = ϵ
    $,
  ),
  caption: [
    The strong next falls over the end of the trace. FLTL decides $bold(X)$ and
    $overline(bold(X))$ from the position of the horizon alone, so
    $semf(u tack.rr bold(X) "true") = bot$ even though every continuation satisfies it.
  ],
) <fig-horizon>

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
    $φ ≡ bold(G) (r -> bold(F) a)$ on a run that keeps requesting. The two continuations of the
    same prefix disagree, so no final verdict is warranted -- yet FLTL must pick one, and its
    $bot$ after the trailing $r$ is indistinguishable from an irrecoverable violation.
  ],
) <fig-futures>

== Maxims for Runtime Verification

A semantics meant for monitoring finite, still-growing traces should respect four
maxims.

+ *Existential next.* Saying "$φ$ holds at the next step" presupposes that a next
  step exists — and on a finite trace we may simply have run out of events. The
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
  finite trace must already be evaluated to that verdict — there is nothing left
  to wait for.

== Syntax and Semantics


#definition([Truth domain $bb(B)_4$], label: <def:b4>)[
  The truth domain of #fltl4 is the four valued set
  $ bb(B)_4 = { top, top^p, bot^p, bot } $
  where $top$ (resp. $bot$) denotes the definitive verdict _true_ (resp. _false_) and
  $top^p$ (resp. $bot^p$) the presumable verdict _presumably true_ (resp.
  _presumably false_). It is a finite distributive de Morgan lattice
  $(bb(B)_4, subset.sq)$, hence a truth domain in the sense of @def:truth-dom[-], ordered
  by
  $ bot subset.sq bot^p subset.sq top^p subset.sq top $
  with $inter.sq$ and $union.sq$ the meet and join of that order, and with
  complementation
  $
    overline(top) = bot quad overline(top^p) = bot^p quad overline(bot^p) = top^p quad overline(bot) = top
  $
]

Note that $bb(B)_4$ is _not_ a Boolean lattice: the presumable verdicts satisfy
$top^p union.sq overline(top^p) = top^p union.sq bot^p = top^p != top$, and dually
$bot^p inter.sq overline(bot^p) = bot^p != bot$. This is precisely what lets a monitor
report a verdict that is not yet final.

#definition([Syntax of #fltl4 formulae], label: <def:fltl4-syntax>)[
  Let $Σ = 2^bold("AP")$ be the finite alphabet built over a finite set of atomic
  propositions $bold("AP")$, with $p ∈ bold("AP")$ an atomic proposition and
  $a ∈ Σ$ a letter. The set of #fltl4 formulae is inductively defined by the following
  grammar:
  $
    φ, ψ ::= b | p | ¬ φ | φ and ψ | φ or ψ | bold(X) φ | overline(bold(X)) φ
    | φ bold("U") ψ | φ bold("R") ψ | bold(F) φ | bold(G) φ
    quad "where " b ∈ bb(B)_4
  $
  In contrast to LTL (@def:ltl-syntax[-]), the constants range over the whole of
  $bb(B)_4$, which is oftenconsidered in the context of multi-valued logics , and $bold(F)$ and $bold(G)$ are taken as primitive operators rather than
  as abbreviations.
]

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
                                                 bot^p & "else"
                                               ) \
          sem(w tack.rr overline(bold(X)) φ) & = cases(
                                                 sem(w^2 tack.rr φ) & "if " abs(w) > 1,
                                                 top^p & "else"
                                               )
        $
      ],
    )

    #block(width: 100%)[
      #align(left, fgrp[until/release])
      $
        sem(w tack.rr φ bold("U") ψ) & = union.sq.big_(1 <= i <= abs(w)) (
                                         sem(w^i tack.rr ψ) inter.sq inter.sq.big_(1 <= j < i) sem(w^j tack.rr φ)
                                       )
                                       union.sq (
                                         bot^p inter.sq inter.sq.big_(1 <= i <= abs(w)) sem(w^i tack.rr φ)
                                       ) \
                                     \
        sem(w tack.rr φ bold("R") ψ) & = union.sq.big_(1 <= i <= abs(w)) (
                                         sem(w^i tack.rr φ) inter.sq inter.sq.big_(1 <= j <= i) sem(w^j tack.rr ψ)
                                       )
                                       union.sq (
                                         top^p inter.sq inter.sq.big_(1 <= i <= abs(w)) sem(w^i tack.rr ψ)
                                       )
      $

      #align(left, fgrp[finally/globally])
      $
        sem(w tack.rr bold(F) φ) & = bot^p union.sq union.sq.big_(1 <= i <= abs(w)) sem(w^i tack.rr φ) \
        sem(w tack.rr bold(G) φ) & = top^p inter.sq inter.sq.big_(1 <= i <= abs(w)) sem(w^i tack.rr φ)
      $
    ]
  ],
  caption: [Semantics of #fltl4 formulae over a non-empty finite trace $w = w_1 dots w_(abs(w)) ∈ Σ^+$],
) <fig-fltl4-sem>

#definition([Semantics of #fltl4], label: <def:fltl4-sem>)[
  The truth value of an #fltl4 formula $φ$ w.r.t. $w$, denoted with $sem(w tack.rr φ)$, is given by the function
  $
    sem(- tack.rr -) : Σ^+ × #fltl4 -> bb(B)_4
  $
  which is defined inductively as shown in @fig-fltl4-sem.
]

Where FLTL falls back on $bot$ and $top$ when the trace runs out (@fig-fltl4-sem, cases
$abs(w) = 1$ for the next operators, and the second disjunct of until/release), #fltl4
falls back on the presumable verdicts $bot^p$ and $top^p$ instead. A definitive verdict
is therefore emitted only when the observed prefix alone already settles the formula,
which is what impartiality asks for.

== Monitor as a Mealy machine

A monitor is a procedure that consumes the input letter by letter and outputs the semantics of the trace read so far with respect to the formula the monitor was built for.
For each temporal formula registered to the `monitor` it is then compiled into a Mealy machine, also called #acr("FSM").

#definition("Mealy machine", label: <def:mealy>)[
  A Mealy machine is a tuple  $cal(M) = (S, s_0, Σ, Γ, δ)$:
  - $S$ a finite set of states,
  - a start state $s_0 ∈ S$,
  - Σ is a finite set called the input alphabet,
  - Γ is the output alphabet and,
  - $delta : Sigma times S -> Gamma times S$ is the transition function.
]

we are now ready to define the monitor  #acr("FSM") #M4 computing the #fltl4 semantics in @def:fltl4-sem[-].

#definition([#acr("FSM") #M4], label: <def:m4>)[
  A `monitor` for #fltl4 is defined by the tuple $cal(M)_4^phi = (S, s_0, Σ, bb(B)_4, delta_4)$ with the following transition function:

  #grid(
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
  where _nrm_ is a normalisation function of a formula $phi$ that eliminate any redundancy present in the formula.
]

Following the characterization of #fltl4, we can etablish a correspondance between #fltl4 semantics and #acr("FSM") $cal(M)$.

#theorem()[
  Let $phi$ be an #fltl4 formula. Then there is an effective procedure constructing an an FSM $cal(M)_4^phi = (S, s_0, Σ, bb(B)_4, delta_4)$ such that for all $u ∈ Σ^*$ the following holds:
  $
    delta_4(s,u) = [ u tack.rr phi ]_4
  $
]

= Enhanced #M4

// In this section we will show how we can improve the #M4 to tackle problems such as mechanising the Anticipation maxime.

First, we present the coalgebraic aspect of Mealy machine @mealy-coalg @bonchi2026effectfulmealymachines. Let $A$ be a finite set and let $B$ be a (possibly infinite) meet-semilattice. A Mealy machine (S, $f$) with inputs in A and outputs in B consists of a set of states $S$ together with a function:
$
  f:S -> (B times S)^A
$
Such a map $f$ is equivalent to the _uncurried_ map between cartesian product $("out", "next"): A times S -> B times S$.
In coalgebraic terms, a Mealy machine $cal(M)(S, f)$ is  a coalgebra of the functor $frak(M): "Set" -> "Set"$ defined, for any set X, as $frak(M)(X) = (B times X)^A$.

#definition(label: <def:mealy-coalg>)[
  A $frak(M)$-_coalgebra_ is a pair $(C, gamma)$, where $C$ is a set (of states) and $gamma: X -> frak(M)(X)$ is a (transition) function.
]

#definition("Mealy homomorphism", label: <def:mealy-hom>)[
  A homomorphism from a Mealy machine $(S, f)$ to a Mealy machine $(T, g)$ is a function $h: S -> T$ preserving initial outputs and next states:
  $
    g compose h = frak(M)(h) compose f, quad "where " frak(M)(h) = ("id"_B times h)^A
  $
]

We adopt the notation $s xarrow(sym: -->, a|b) s'$ to denotes the (transition) function result $f(s)(a) = ⟨b, s'⟩$.


== #M4 compositions and pre-post treatments with Profunctor

In @def:mealy[-], the set of input and output language are fixed and without side-effect.
A potential property would be to make them parametric or dynamically computed.
Both intentions are captured by reading a Mealy machine as an element of a _profunctor_
@benabou2000distributors, contravariant in the input alphabet (the pre-treatment) and covariant in
the output alphabet (the post-treatment).

#definition([$cal(M)(X)$ profunctor], label: <def:mealy-prof>)[
  A _profunctor_ $phi : cal(C) arrow.r.not cal(D)$ is a functor
  $phi : cal(D)^"op" times cal(C) -> "Set"$ @benabou2000distributors. An element of $phi(d, c)$ is
  a _heteromorphism_ $d -> c$ (not a morphism of $cal(C)$ nor of $cal(D)$).
  For $f : d -> d' in cal(D)$, $g : c -> c' in cal(C)$ and $x in phi(d', c)$, the two actions
  are written as juxtaposition, $x f in phi(d, c)$ and $g x in phi(d', c')$.
  Writing $frak(M)_(A,B)(X) = (B times X)^A$, the Mealy profunctor
  $
    Mly : "Set"^"op" times "Set" -> "Set", quad
    Mly(A, B) := nu X. #h(.2em) (B times X)^A
  $
  sends $(A, B)$ to the Mealy behaviours from the input alphabet $A$ to the output alphabet $B$.
  Being a final coalgebra, $Mly(A, B) tilde.equiv (B times Mly(A, B))^A$, so a heteromorphism can
  be applied; write $m(a) = ⟨b, m'⟩$ for one unfolding. Its two actions, for $f : A' -> A$ and
  $g : B -> B'$, are then given corecursively by
  $
    (m f)(a') & = ⟨b, m' f⟩, quad    & "where" ⟨b, m'⟩ = m(f(a')) \
     (g m)(a) & = ⟨g(b), g m'⟩, quad &     "where" ⟨b, m'⟩ = m(a)
  $
  so that $m f in Mly(A', B)$ and $g m in Mly(A, B')$.
]

=== Pre- and post-treatment

The two actions of @def:mealy-prof[-] _are_ the pre- and the post-treatment of a machine. Both
keep $S$ and $s_0$ and only rewire the transition, which is why neither can enlarge #M4.

#definition([Actions on #M4], label: <def:actions>)[
  On a machine presentation, the right action $m f in Mly(A', B)$ (pre-treatment) and the left
  action $g m in Mly(A, B')$ (post-treatment) keep $S$ and $s_0$ and rewire the transition:
  #align(center, grid(
    columns: (auto, auto),
    column-gutter: 2.4em,
    align: horizon,
    prooftree(rule(
      label: [pre],
      $s tr(f(a'), b) s'$,
      $s tr(a', b) s'$,
    )),
    prooftree(rule(
      label: [post],
      $s tr(a, b) s'$,
      $s tr(a, g(b)) s'$,
    )),
  ))
]

#definition([Mealy composition], label: <def:mly-comp>)[
  Profunctors compose by tracing out the middle object with a _coend_ @coend. We write that
  composition $seq$, in diagrammatic order, so that $phi seq psi$ is "$phi$ first, then $psi$".
  The two composite $Mly$ profunctors $phi: A arrow.r.not B in Mly(A, B)$ and $psi: B arrow.r.not C in Mly(B, C)$ is given by:
  $
    (Mly seq Mly)(A, C) = integral^B Mly(A, B) times Mly(B, C).
  $
  A representative is a pair $(m, n)$ with $m in Mly(A, B)$ and $n in Mly(B, C)$ for some $B$, and
  the coend identifies $(g m, n)$ with $(m, n g)$ for every $g : B -> B'$, $m in Mly(A, B)$ and
  $n in Mly(B', C)$. The same symbol carries the induced operation on heteromorphisms,
  $m seq n in Mly(A, C)$: composing the two profunctors and composing two machines are one
  operation read at two levels.
]

#figure(
  placement: top,
  stack(
    dir: ttb,
    spacing: 2.4em,

    // ── (a) the two actions are pure boxes on either side of m ──────────
    diagram(
      spacing: (2.9em, 1.4em),
      node-outset: 1pt,
      node((0, 0), elbl($A'$, caxis), name: <pa>),
      mbox((1, 0), text(size: .92em, $"arr"(f)$), name: <pf>),
      sbox((2, 0), text(size: .92em, $m$), cteal, name: <pm>),
      mbox((3, 0), text(size: .92em, $"arr"(g)$), name: <pg>),
      node((4, 0), elbl($B'$, caxis), name: <pb>),
      edge(<pa>, <pf>, "->", stroke: cgray + .6pt),
      edge(<pf>, <pm>, elbl($A$, caxis), "->", stroke: cgray + .6pt),
      edge(<pm>, <pg>, elbl($B$, caxis), "->", stroke: cgray + .6pt),
      edge(<pg>, <pb>, "->", stroke: cgray + .6pt),
      compbox((<pf>, <pm>, <pg>)),
      node((2, 1.25), dtext(size: .76em)[$g m f$ — the state space $S$ of $m$ is untouched]),
    ),

    // ── (b) composition hides the middle alphabet and the state ─────────
    diagram(
      spacing: (3.4em, 1.4em),
      node-outset: 1pt,
      node((0, 0), elbl($A$, caxis), name: <sa>),
      sbox((1, 0), text(size: .92em, $m$), cteal, name: <sm>),
      sbox((2, 0), text(size: .92em, $n$), camber, name: <sn>),
      node((3, 0), elbl($C$, caxis), name: <sc>),
      edge(<sa>, <sm>, "->", stroke: cgray + .6pt),
      edge(<sm>, <sn>, elbl($B$, caxis), "->", stroke: cgray + .6pt),
      edge(<sn>, <sc>, "->", stroke: cgray + .6pt),
      compbox((<sm>, <sn>)),
      node((1.5, 1.25), dtext(size: .76em)[$m seq n$ — $B$ and $S times T$ are both inside the box]),
    ),

    // ── (c) the coend identification: g slides across the junction ──────
    diagram(
      spacing: (3.3em, 1.4em),
      node-outset: 1pt,
      // left wiring: (g m, n)
      sbox((0, 0), text(size: .92em, $m$), cteal, name: <lm>),
      mbox((1, 0), text(size: .92em, $g$), name: <lg>),
      sbox((2, 0), text(size: .92em, $n$), camber, name: <ln>),
      edge(<lm>, <lg>, elbl($B$, caxis), "->", stroke: cgray + .6pt),
      edge(<lg>, <ln>, elbl($B'$, caxis), "->", stroke: cgray + .6pt),
      compbox((<lm>, <lg>), inset: 9pt),
      node((.5, 1.35), dtext(fill: ctealD, size: .76em)[$(g m, n)$]),

      node((3, 0), text(size: 1.1em, fill: cgray, $tilde$)),

      // right wiring: (m, n g)
      sbox((4, 0), text(size: .92em, $m$), cteal, name: <rm>),
      mbox((5, 0), text(size: .92em, $g$), name: <rg>),
      sbox((6, 0), text(size: .92em, $n$), camber, name: <rn>),
      edge(<rm>, <rg>, elbl($B$, caxis), "->", stroke: cgray + .6pt),
      edge(<rg>, <rn>, elbl($B'$, caxis), "->", stroke: cgray + .6pt),
      compbox((<rg>, <rn>), inset: 9pt),
      node((5.5, 1.35), dtext(fill: camberD, size: .76em)[$(m, n g)$]),
    ),
  ),
  caption: [
    The two actions and the composition of @def:mly-comp[-], read as wiring.
  ],
) <fig-prof-wiring>



== Anticipation as a futumorphism <sec-anticipation>

We restate the fourth of our maxims "Anticipation: the moment every infinite continuation of the observed prefix agrees on one verdict, the finite trace must already be evaluated to that verdict". The monitor of @def:m4[-] does not satisfy such property. Being an $frak(M)$-coalgebra, it is unfolded by an _anamorphism_ @yang2022fantasticmorphismsthemguide, and an anamorphism produces exactly one layer of $Mly(Σ, bb(B)_4)$ per transition of $delta_4$, so the machine only ever commits to the verdict of the step it is currently taking. Anticipation asks for the opposite commitment. The corecursion scheme that grants precisely this is the _futumorphism_ @yang2022fantasticmorphismsthemguide. A futumorphism returns a finite _plan_ — several layers already built — and consults the seed again only at the leaves of that plan. Plans are the elements of the free monad of $frak(M)$.

// 𝔐(−) : Ob(Set) → Ob(Set),    𝔐(Y) = (B × Y)^A
// 𝔐(−) : Hom(S, T) → Hom(𝔐(S), 𝔐(T)),    𝔐(h) = (id_B × h^A
#definition([Plans $Fre$], label: <def:free-mealy>)[
  The _free monad_ of $frak(M)$ sends a set $X$ of seeds to the least fixed point
  $
    Fre (X) = mu Y. #h(.2em) X + frak(M)(Y) = mu Y. #h(.2em) X + (B times Y)^A
  $
  with the two constructors
  $
    eta : X -> Fre (X), quad "op" : frak(M)(Fre (X)) -> Fre (X).
  $
  We call an element of $Fre (X)$ a _plan_. The plan $eta(x)$ is "resume from the seed $x$"; the plan $"op"(t)$ is "make the transitions prescribed by the layer $t in (B times Fre (X))^A$, then carry on with the plans it leaves behind". Since $Fre (X)$
  is a _least_ fixed point, every branch of a plan is finite and ends in a seed: a plan performs only a finite number of lookahead steps.
]

#definition([$frak(M)$-futumorphism], label: <def:futu>)[
  An _anticipating coalgebra_ on a set $S$ is a map
  $
    gamma : S -> frak(M)(Fre (S))
  $
  that is, a coalgebra allowed to answer with plans rather than with bare seeds. Every plan
  can itself be resumed, which turns $gamma$ into an ordinary $frak(M)$-coalgebra on plans:
  $
    gamma^dagger : Fre (S) -> frak(M)(Fre (S)) \
    gamma^dagger (eta(s)) = gamma(s) quad gamma^dagger ("op"(t)) = t.
  $
  The first case expands a seed $s$ by consulting $gamma$; the second hands back a layer
  $t$ the plan already prescribes, as it stands, without consulting $gamma$ again. The two
  cases say exactly that $gamma^dagger$ extends $gamma$ along $eta$ (@fig-futu-resume).
  Because $Mly(A, B)$ is the final $frak(M)$-coalgebra (@def:mealy-prof[-]), $gamma^dagger$ has a unique homomorphism $"ana"(gamma^dagger)$ into it, and the
  _futumorphism_ of $gamma$ is its restriction to seeds:
  $
    "futu" : (S -> frak(M)(Fre space S)) -> S -> Mly(A, B) \
    "futu"(gamma) := "ana"(gamma^dagger) compose eta #h(.6em) : #h(.6em) S -> Mly(A, B).
  $
]

#figure(
  placement: top,
  diagram(
    spacing: (5.6em, 2.4em),
    node-outset: 3pt,
    node((0, 0), $S$, name: <ta>),
    node((1, 0), $Fre (S)$, name: <tb>),
    node((2, 0), $frak(M)(Fre (S))$, name: <tc>),
    edge(<ta>, <tb>, elbl($eta$, caxis), "->", stroke: cgray + .6pt),
    edge(<tb>, <tc>, elbl($gamma^dagger$, caxis), "->", stroke: cgray + .6pt),
    edge(<ta>, <tc>, elbl($gamma$, caxis), "->", bend: -38deg, stroke: cgray + .6pt),
  ),
  caption: [
    A seed is the shallowest plan, so plans unfold like seeds.
  ],
) <fig-futu-resume>

The isomorphism $Mly(A, B) tilde.equiv frak(M)(Mly(A, B))$ makes $Mly(A, B)$ an
$frak(M)$-algebra, and therefore a $Fre$-algebra:
$
  flat : Fre (Mly(A, B)) -> Mly(A, B)
$
which _flattens a plan into the behaviour it denotes_: it makes the transitions the plan
prescribes, layer by layer, and on reaching a leaf carries on with the behaviour sitting
there. Since $Fre (h)$ relabels the leaves of a plan over $S$ with behaviours,
$flat compose Fre (h) : Fre (S) -> Mly(A, B)$ sends a plan to the behaviour it denotes. In
terms of it, $"futu"(gamma)$ is the unique $h : S -> Mly(A, B)$ making
$
  "out" compose h = frak(M)(flat compose Fre (h)) compose gamma
$
commute (@fig-futu-square), which is the universal property we appeal to below. Restricting $gamma$ to plans of
the form $eta(s)$ collapses this to $"out" compose h = frak(M)(h) compose gamma$, the homomorphism condition of @def:mealy-hom[-]: the futumorphism is a conservative extension of
the unfolding already used for #M4.
To show that #M4 is an instance of $frak(M)$-futumorphism we still need to know when a verdict may be committed to.
The _residual_ formula (i.e. the n-th approximation) carries that information.

#figure(
  placement: bottom,
  diagram(
    spacing: (8.4em, 3.8em),
    node-outset: 3pt,
    node((0, 0), $S$, name: <ua>),
    node((1, 0), $frak(M)(Fre (S))$, name: <ub>),
    node((0, 1), $Mly(A, B)$, name: <uc>),
    node((1, 1), $frak(M)(Mly(A, B))$, name: <ud>),
    edge(<ua>, <ub>, elbl($gamma$, caxis), "->", stroke: cgray + .6pt),
    edge(
      <ua>,
      <uc>,
      elbl($h = "futu"(gamma)$, ctealD),
      "-->",
      label-side: right,
      stroke: ctealD + .7pt,
    ),
    edge(<ub>, <ud>, elbl($frak(M)(flat compose Fre (h))$, caxis), "->", stroke: cgray + .6pt),
    edge(<uc>, <ud>, elbl($"out" #h(.25em) (tilde.equiv)$, caxis), "->", stroke: cgray + .6pt),
  ),
  caption: [
    How the anticipating behaviour $"futu"(gamma) in Mly(A, B)$ is constructed from $gamma$.
  ],
) <fig-futu-square>

#definition([Decided residual], label: <def:decided>)[
  A formula $phi$ is _decided_ on $b in bb(B)_2 subset bb(B)_4$, written $"dec"(phi) = b$, when every
  infinite word agrees on it:
  $
    "dec"(phi) = b quad "iff" quad forall w in Σ^ω. #h(.3em) sem(w tack.rr phi) = b
  $
  and $"dec"(phi) = #h(.15em) ?$ (_undecided_) when no such $b$ exists. Deciding $phi$ is an
  LTL validity check, and the residuals reachable from $phi$ under $delta_4$ form a finite
  set, so $"dec"$ is a finite table computed once, when the monitor is built.
]

#lemma([$delta_4$ computes the residual], label: <lem:residual>)[
  Write $delta_4^*(u, phi)$ for the formula component of $delta_4$ iterated along
  $u in Σ^*$. Then for every finite prefix $u in Σ^*$ and every infinite continuation
  (suffix) $w in Σ^ω$ of $u$,
  $
    semw(u w tack.rr phi) = semw(w tack.rr delta_4^*(u, phi)).
  $
]

Consequently the assertion that every infinite continuation of $u$ agrees on $b$" is interpreted as $"dec"(delta_4^*(u, phi)) = b$.

#definition([Anticipating monitor $cal(M)_4^(phi, k)$], label: <def:m4-futu>)[
  Fix a _threshold_ $k >= 1$ and take #fltl4 formulae as seeds, so the coalgebra to be built
  has the shape $#fltl4 -> frak(M)(Fre (#fltl4))$ asked for by @def:futu[-]. A definitive verdict $b in {top, bot} subset.eq bb(B)_4$ is also a _formula_ therefore a final verdict has the canonical (transition) form:
  $
    delta_4(a, b) = (b, b) #h(.6em) in #h(.6em) bb(B)_4 times #fltl4
    quad "for every " a in Σ .
  $
  A step is parametric in a _continuation_
  $
    kappa : #fltl4 -> Fre (#fltl4)
  $
  which decides how to carry on from a residual that is still undecided: given such a
  residual it returns the plan to be followed from there. Given $kappa$, the step
  $
    "step"_kappa : #fltl4 -> frak(M)(Fre (#fltl4))
  $
  reads a letter $a in Σ$, takes the ordinary transition $(v, phi') = delta_4(a, phi)$, and
  answers
  $
    "step"_kappa (phi)(a) = cases(
      ⟨b, eta(b)⟩ & "if " "dec"(phi') = b in bb(B)_2 quad & ("commit"),
      ⟨v, kappa(phi')⟩ & "if " "dec"(phi') = #h(.15em) ? quad & ("defer to" kappa)
    )
  $
  In the first case, the residual is settled (@def:decided[-]), so the step overrides the
  verdict $v$ that $delta_4$ would have emitted, outputs the definitive $b$ instead, and
  collapses to the bare constant seed $eta(b)$ ignoring the continuation $kappa$. In the second case the residual is still open, so the step keeps $delta_4$'s own verdict $v$ and
  hands $phi'$ to $kappa$ to be developed further.
  Therefore, iterating on the step deepens the plan. 
  We write $"plan"_j : #fltl4 -> Fre (#fltl4)$ for the continuation that unfold $j$ layers:
  $
    "plan"_0 = eta, quad "plan"_(j+1) = "op" compose "step"_("plan"_j) .
  $
  Finally, the anticipating coalgebra and the machine it denotes are then:
  $
    gamma_4^k := "step"_("plan"_(k-1)) #h(.5em) : #h(.5em) #fltl4 -> frak(M)(Fre (#fltl4)),
    quad cal(M)_4^(phi, k) := "futu"(gamma_4^k)(phi) #h(.3em) in #h(.3em) Mly(Σ, bb(B)_4).
  $
  The horizon is an operational knob only: the verdicts do not depend on it, as
  @prop:anticipation[-] holds for every $k >= 1$ without mentioning $k$ in its conclusions.
  What $k$ buys is how much work is done per move. At $k = 1$ we have $"plan"_0 = eta$, so
  every branch of the plan ends immediately in a seed, the plan is one layer deep,
  $gamma_4^1$ is an ordinary coalgebra and $"futu"(gamma_4^1) = "ana"(gamma_4^1)$ -- the
  free monad buys nothing. A larger $k$ precomputes the whole depth-$k$ decision tree over
  the next $k$ letters in a single move, amortising the run of the machine over blocks of
  $k$ letters.
]

#proposition([$cal(M)_4^(phi, k)$ satisfies Anticipation], label: <prop:anticipation>)[
  Let $phi$ be an #fltl4 formula, let $k >= 1$, let $u = u_1 dots u_n in Σ^+$, and let
  $b_n in bb(B)_4$ be the $n$-th output of $cal(M)_4^(phi, k)$ on $u$. Then
  + _(soundness)_ if $b_n in {top, bot}$ then $semw(u w tack.rr phi) = b_n$ for every
    $w in Σ^ω$;
  + _(anticipation)_ conversely, if $semw(u w tack.rr phi) = b$ for every $w in Σ^ω$ and some
    $b in {top, bot}$, then $b_n = b$;
  + _(agreement)_ if no prefix of $u$ has a decided residual, then $b_n = sem(u tack.rr phi)$,
    the verdict of @def:fltl4-sem[-].

]

== Final picture of Enhanced #M4



The three enhancements are three readings of one object, and they stack without interfering.
Fix a formula $phi$, a horizon $k >= 1$, a pre-treatment $f : A -> Σ$ and a post-treatment
$g : bb(B)_4 -> B$. The enhanced monitor is the single heteromorphism
$
  cal(M)_4^(phi, k) [f, g] := g #h(.15em) "futu"(gamma_4^k)(phi) #h(.15em) f
  #h(.5em) in #h(.5em) Mly(A, B)
$
unfolded from the single anticipating coalgebra
$
  gamma_4^k : #fltl4 -> frak(M)_(Σ, bb(B)_4)(Fre (#fltl4)),
  quad "where" quad frak(M)_(A, B)(X) = (B times X)^A .
$

Each layer contributes one thing and nothing else:

#grid(
  columns: (auto, 1fr),
  column-gutter: 1.2em,
  row-gutter: .8em,
  [_coalgebra_ (@def:mealy-coalg[-])],
  [
    hides the state: a machine is known only through the unique map into the final
    coalgebra $Mly(Σ, bb(B)_4) = nu X. #h(.2em) (bb(B)_4 times X)^Σ$, so two monitors with
    different state spaces but equal verdicts are equal.
  ],

  [_profunctor_ (@def:mealy-prof[-])],
  [
    makes the two alphabets parameters: $f$ and $g$ rewire the transition without touching
    $S$ or $s_0$ (@def:actions[-]), and $seq$ composes monitors by tracing out the middle
    alphabet (@def:mly-comp[-]).
  ],

  [_futumorphism_ (@def:futu[-])],
  [
    lets the coalgebra answer with plans instead of seeds, which is what allows a verdict to
    be committed before the step that would otherwise reveal it (@prop:anticipation[-]).
  ],
)

Setting $k = 1$ and $f = "id"_Σ$, $g = "id"_(bb(B)_4)$ collapses every layer at once and
returns the #M4 of @def:m4[-]: the enhancements are extensions, not replacements.

= Development Overview <sec-dev>

// = Canonical simplification `smplfy` as a term rewriting system <sec-smplfy>

// We realise `smplfy` as a term rewriting system (TRS) $cal(R)$ on `FLTL₄`
// formulae. Reduction drives a formula toward a normal form; we prove that
// $cal(R)$ is _terminating_ and _confluent modulo the associativity and
// commutativity of $and$ and $or$_, so every formula has a unique normal form and
// `smplfy` is a well-defined function.

// Throughout we assume the input is in negation normal form (NNF): $not$ occurs
// only on atomic propositions. This invariant is established by the `nnf` pre-pass
// and preserved by $delta_4$, hence a literal $p$ or $not p$ is treated as an
// atomic constant by $cal(R)$.

// == Rewrite rules

// We split $cal(R) = cal(R)_s union cal(R)_d$ into a _simplification core_
// $cal(R)_s$ (rules 1–24) and an optional _distribution_ layer $cal(R)_d$
// (rules 25–26).

// #grid(
//   columns: (1fr, 1fr),
//   column-gutter: 1.5em,
//   $
//      "true" and phi & -> phi     &  quad (1) \
//      phi and "true" & -> phi     &  quad (2) \
//     "false" and phi & -> "false" &  quad (3) \
//     phi and "false" & -> "false" &  quad (4) \
//         phi and phi & -> phi     &  quad (5) \
//       "true" or phi & -> "true"  &  quad (6) \
//       phi or "true" & -> "true"  &  quad (7) \
//      "false" or phi & -> phi     &  quad (8) \
//      phi or "false" & -> phi     &  quad (9) \
//          phi or phi & -> phi     & quad (10)
//   $,
//   $
//     phi and (phi or psi) & -> phi     & quad (11) \
//     (phi or psi) and phi & -> phi     & quad (12) \
//     phi or (phi and psi) & -> phi     & quad (13) \
//     (phi and psi) or phi & -> phi     & quad (14) \
//                 F "true" & -> "true"  & quad (15) \
//                G "false" & -> "false" & quad (16) \
//             phi U "true" & -> "true"  & quad (17) \
//            phi R "false" & -> "false" & quad (18) \
//            "false" U psi & -> psi     & quad (19) \
//             "true" R psi & -> psi     & quad (20) \
//             "true" U psi & -> F psi   & quad (21) \
//            "false" R psi & -> G psi   & quad (22) \
//                F (F phi) & -> F phi   & quad (23) \
//                G (G phi) & -> G phi   & quad (24)
//   $,
// )

// Rules (11)–(14) are stated up to the commutativity of $and$ and $or$; their
// four mirror-image variants are included. The distribution layer is:

// $
//   phi and (psi or chi) & -> (phi and psi) or (phi and chi) & quad (25) \
//   (phi or psi) and chi & -> (phi and chi) or (psi and chi) & quad (26)
// $

// #block(inset: (left: 0pt))[
//   *Remark (soundness in $bb(B)_4$).* Because $(bb(B)_4, ⊑)$ is a De Morgan but
//   _not_ a Boolean lattice, the complement laws are inadmissible: taking
//   $phi = ⊤ₚ$ gives $phi or not phi = ⊤ₚ ⊔ ⊥ₚ = ⊤ₚ != ⊤$ and
//   $phi and not phi = ⊤ₚ ⊓ ⊥ₚ = ⊥ₚ != ⊥$. Likewise, temporal operators whose
//   constant argument evaluates to a _presumable_ value are left un-folded, since
//   $⊤ₚ, ⊥ₚ$ are not formulae: $sem(w tack.rr F "false") = ⊥ₚ != ⊥$ and
//   $sem(w tack.rr G "true") = ⊤ₚ != ⊤$, whereas the absorbing cases (15)–(18) do
//   collapse to $"true" slash "false"$. Every rule above was validated against the
//   semantics $sem(-)$ and the step relation $delta_4$.
// ]

// == Mealy machines as a profunctor

#bibliography("refs.bib")
