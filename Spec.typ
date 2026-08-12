#import "@preview/mmdr:0.2.2": mermaid
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/codly:1.3.0"
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set


// a Mealy machine drawn as a box
#let mbox = (pos, lbl) => node(pos, lbl, shape: fletcher.shapes.rect, stroke: .6pt, inset: 9pt)
#let compbox = enc => node(enclose: enc, stroke: (paint: gray, dash: "dashed", thickness: .6pt), inset: 16pt)


#set document(title: [FLTL₄ Monitor])

#let fltl4 = `FLTL₄`

#show heading.where(level: 1): set heading(numbering: "1")


#set page(
  numbering: "1",
  number-align: center + bottom, // Places number in the header
)

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
// ---------- end diagram kit ----------

= Introduction

This document aims to specify the development of a `monitor` to verify if program guarantee some
temporal assertions defined in the Finite Temporal Linear Logic 4 (LTL4), a suitable temporal logic for runtime verification @rv-ltl.


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
        text(size: .9em, fill: cpurpD, $tack.r space square (A -> diamond B)$),
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
        vmark(sym.checkmark, cteal, [⊤]),
        vmark(sym.checkmark, camberD, [⊤ₚ], size: .95em),
        vmark(sym.crossmark, camberD, [⊥ₚ], size: .95em),
        vmark(sym.crossmark, cred, [⊥]),
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
  caption: [The runtime-verification loop: a property $tack.r square (A -> diamond B)$ is compiled
    into a `monitor`, which observes the instrumented system and emits a verdict in $bb(B)_4$ after
    every event — a definitive $⊤ slash ⊥$, or, while some continuation could still swing the answer,
    a presumable $⊤ₚ slash ⊥ₚ$.],
) <fig-rv-loop>

== Overview



= Preliminaries

= #fltl4

== Maxims for Runtime Verification

A semantics meant for monitoring finite, still-growing traces should respect four
maxims. They are what force the four-valued domain $bb(B)_4$ upon us.

+ *Existential next.* Saying "$φ$ holds at the next step" presupposes that a next
  step exists — and on a finite trace we may simply have run out of events. The
  logic therefore needs a _strong_ next $bold(X)$, which refuses to hold when the
  trace stops here, alongside the _weak_ next $overline(bold(X))$, which accepts
  it.

+ *Complementation by negation.* Negating a formula must really flip its verdict:
  $not φ$ evaluates to the complement of $φ$'s verdict, and that complement is
  always a _different_ value. No verdict may be its own complement — which is why
  a single "don't know" value will not do, and why the presumable verdicts come
  in the pair $⊤ₚ$ / $⊥ₚ$.

+ *Impartiality.* A monitor must not jump to conclusions. As long as some
  infinite continuation of what we have seen so far would lead to a different
  answer, the trace must not be given a final $⊤$ or $⊥$; the most it may say is
  "true (false) so far", i.e. $⊤ₚ$ ($⊥ₚ$).

+ *Anticipation.* Conversely, a monitor must not sit on a conclusion it can
  already draw. The moment every infinite continuation agrees on one verdict, the
  finite trace must already be evaluated to that verdict — there is nothing left
  to wait for.

== Syntax

Let $Σ = 2^("AP")$ be the finite alphabet, p ∈ AP an atomic proposition, a ∈ Σ a letter. We define the syntax of the #fltl4 logic:

$
  bb(B)_4 & ::= {⊤, ⊤ₚ, ⊥ₚ, ⊥} \
     φ, ψ & ::= bb(B)_4 | p | φ and ψ | φ or ψ | ¬ φ | bold(X) φ | overline(bold(X)) φ | φ bold("U") ψ | φ bold("R") ψ
            | φ bold("G") ψ | bold("F") ψ
$

The truth domains $bb(B)_4$  is:
- a complete distributed lattice $(bb(B)_4, ⊑)$ with the following inclusion order $⊥ ⊑ ⊥p ⊑ ⊤ₚ ⊑ ⊤$
- and the complement computed as follows:
$
  overline(⊤) = ⊥ quad overline(⊤ₚ) = ⊥ₚ quad overline(⊥ₚ) = ⊤ₚ quad overline(⊥) = ⊤
$

However, $bb(B)_4$ is not a boolean lattice.

== Semantics

#let sem(x) = $lr(⟦ #x ⟧)_4$   // semantic bracket  ⟦ … ⟧₄
$
  sem(-)_ₖ : Σ^+ × "LTL" → bb(B)_4
$
#grid(
  columns: (1fr, 1fr),
  column-gutter: 1.5em,
  $
         sem(w tack.r "true") & = top \
        sem(w tack.r "false") & = bot \
              sem(w tack.r p) & = cases(
                                  top & "if " p in w_1,
                                  bot & "if " p in.not w_1
                                ) \
          sem(w tack.r not p) & = cases(
                                  top & "if " p in.not w_1,
                                  bot & "if " p in w_1
                                ) \
        sem(w tack.r not phi) & = overline(sem(w tack.r phi)) \
     sem(w tack.r phi or psi) & = sem(w tack.r phi) union.sq sem(w tack.r psi) \
    sem(w tack.r phi and psi) & = sem(w tack.r phi) inter.sq sem(w tack.r psi)
  $,
  $
    sem(w tack.r X phi) &= cases(
      sem(w^2 tack.r phi) & "if " abs(w) > 1,
      bot^p & "else"
    ) \
    sem(w tack.r overline(X) phi) &= cases(
      sem(w^2 tack.r phi) & "if " abs(w) > 1,
      top^p & "else"
    ) \
    sem(w tack.r phi U psi) &= union.sq.big_(1 <= i <= abs(w)) ( sem(w^i tack.r psi) inter.sq inter.sq.big_(1 <= j < i) sem(w^j tack.r phi) ) \
    & quad union.sq ( bot^p inter.sq inter.sq.big_(1 <= i <= abs(w)) sem(w^i tack.r phi) ) \
    sem(w tack.r phi R psi) &= union.sq.big_(1 <= i <= abs(w)) ( sem(w^i tack.r phi) inter.sq inter.sq.big_(1 <= j <= i) sem(w^j tack.r psi) ) \
    & quad union.sq ( top^p inter.sq inter.sq.big_(1 <= i <= abs(w)) sem(w^i tack.r psi) ) \
    sem(w tack.r F phi) &= bot^p union.sq union.sq.big_(1 <= i <= abs(w)) sem(w^i tack.r phi) \
    sem(w tack.r G phi) &= top^p inter.sq inter.sq.big_(1 <= i <= abs(w)) sem(w^i tack.r phi)
  $,
)

== Monitor as a Mealy machine

For each temporal formula registered to the `monitor` it is then compiled into a Mealy machine.
Our Mealy machine is the 6-tuple  $(S, s_0, Σ, Γ, δ)$:
- $S$ a ﬁnite set of states,
- a start state $s_0 ∈ S$,
- a finite set called the input alphabet Σ,
- Γ is the output alphabet and
- a transition function $delta_4 : Sigma times "LTL" -> bb(B)_4 times "LTL"$

$
  delta_4 : Sigma times "LTL" -> bb(B)_4 times "LTL"
$

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
     delta_4 (a, phi or psi) & = (v_phi union.sq v_psi, "smplfy" (phi' or psi')) \
    delta_4 (a, phi and psi) & = (v_phi inter.sq v_psi, "smplfy" (phi' and psi'))
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

$
  "smplfy" : "LTL" -> "LTL"
$

= Development overview

The `monitor` reads a stream of events output by an application and verifies after each new event whether a set of #fltl4 formulae hold.


The `monitor` is a set of  well formed #fltl4 formulae and then compiled into a Mealy machine.
Each event emitted by the software is an input shared to all the compiled Mealy machine declared.

The `monitor` is extended to keep a history of the previous evaluation at each time step, enabling evaluation of the next state by looking at the history of previous computations.

== The input event stream

A finite word $w$ is a finite sequence over the alphabet $Σ = 2^("AP")$.

The monitor will read a letter $x ∈ Σ$ as input, apply it to the word $w$, and evaluate the formulas over it. However, for efficiency, the monitor will save the last state and evaluate the newer input over it.


The rewrite rules implementing `smplfy`, together with proofs of termination and
confluence (modulo the associativity and commutativity of $and$ and $or$), are
given in the section _Canonical simplification `smplfy` as a term rewriting
system_ below.

== Mealy machine

A possible implementation in Haskell will be:
```hs
evlFLTL4 :: Char -> FLTL -> (Truth, FLTL)
evlFLTL4 a TTrue = (Top, TTrue)
evlFLTL4 a FFalse = (Bot, FFalse)
evlFLTL4 a (Prop p)
  | a == p = (Top, TTrue)
  | a /= p = (Bot, FFalse)
evlFLTL4 a (Not (Prop p))
  | a == p = (Bot, FFalse)
  | a /= p = (Top, TTrue)
evlFLTL4 a (l :\/ r) = (vl ⊔ vr, l' :\/ r')
  where
    (vl, l') = evlFLTL4 a l
    (vr, r') = evlFLTL4 a r
evlFLTL4 a (l :/\ r) = (vl ⊓ vr,  l' :/\ r')
  where
    (vl, l') = evlFLTL4 a l
    (vr, r') = evlFLTL4 a r
evlFLTL4 a (X p) = (PBot, p)
evlFLTL4 a (Xweak p) = (PTop, p)
evlFLTL4 a (U p q) = (PTop, q :\/ (p :/\ X (U p q)))
evlFLTL4 a (R p q) = (PTop, q :/\ (p :\/ Xweak (R p q)))
evlFLTL4 a (F p) = evlFLTL4 a (p :\/ X (F p))
evlFLTL4 a (G p) = evlFLTL4 a (p :/\ Xweak (G p))
```

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
//   $⊤ₚ, ⊥ₚ$ are not formulae: $sem(w tack.r F "false") = ⊥ₚ != ⊥$ and
//   $sem(w tack.r G "true") = ⊤ₚ != ⊤$, whereas the absorbing cases (15)–(18) do
//   collapse to $"true" slash "false"$. Every rule above was validated against the
//   semantics $sem(-)$ and the step relation $delta_4$.
// ]

// == Mealy machines as a profunctor

// Input and output of the Mealy machine can be preprocessed and postprocessed
// respectively by viewing the machine as a profunctor; properties that depend on
// one another are then combined by profunctor composition.

// === The Mealy bifunctor

// Write $cal(M)(a, b)$ for the set of Mealy machines with input alphabet $a$ and
// output alphabet $b$. It is the carrier of the terminal coalgebra of the functor
// $X |-> (a -> b × X)$, equivalently the final solution of

// $
//   cal(M)(a, b) ≅ a -> (b × cal(M)(a, b)) .
// $

// A monitor for a formula is the element of $cal(M)(Σ, bb(B)_4 × "LTL")$ obtained
// by unfolding the transition $delta_4 : Σ × "LTL" -> bb(B)_4 × "LTL"$ from the
// formula taken as initial state: reading a letter $a ∈ Σ$ returns a verdict in
// $bb(B)_4$ together with the continuation machine that carries the simplified
// residual formula.

// === Profunctor structure

// $cal(M)$ is a profunctor, i.e. a functor

// $
//   cal(M) : bold("Set")^("op") × bold("Set") -> bold("Set"),
// $

// contravariant in the input and covariant in the output. Its action on morphisms
// $f : a' -> a$ and $g : b -> b'$ is the map

// $
//   cal(M)(f, g) : cal(M)(a, b) -> cal(M)(a', b'),
// $

// defined coinductively: it precomposes the input with $f$ and postcomposes the
// output with $g$, recursing on the continuation. Write $partial_m : a -> b$ for
// the _output map_ of a state $m$ — the verdict it emits now, read off the first
// projection of the isomorphism above. On this observable component the action is
// plain pre- and post-composition:

// #align(center, diagram(
//   spacing: (3.6em, 3em),
//   mbox((0, 0), $f$),
//   mbox((1, 0), $m$),
//   mbox((2, 0), $g$),
//   edge((-1, 0), (0, 0), $a'$, "->"),
//   edge((0, 0), (1, 0), $a$, "->"),
//   edge((1, 0), (2, 0), $b$, "->"),
//   edge((2, 0), (3, 0), $b'$, "->"),
//   compbox(((0, 0), (2, 0))),
//   node((1, -0.8), text(fill: gray, size: .82em)[$m' = cal(M)(f,g)(m)$]),
// ))

// The core machine $m$ is bracketed by the pre-adapter $f$ ($=$ `lmap`) and the
// post-adapter $g$ ($=$ `rmap`); the dashed box is the re-typed machine
// $m' = cal(M)(f, g)(m)$, whose output map is $partial_(m') = g ∘ partial_m ∘ f$.
// On a full input $x$ this reads $cal(M)(f, g)(m)(x) = (g(partial_m (f x)),
//   cal(M)(f, g)(m'))$. This is `dimap`. Functoriality gives the profunctor laws

// $
//   cal(M)("id", "id") = "id", quad
//   cal(M)(f ∘ f', g' ∘ g) = cal(M)(f', g') ∘ cal(M)(f, g),
// $

// so re-typing the boundary never alters the state nor the transition $delta_4$.
// The two one-sided actions are the preprocessing and postprocessing maps:

// $
//   "lmap" f = cal(M)(f, "id") quad (f : e -> Σ), quad quad
//   "rmap" g = cal(M)("id", g) quad (g : bb(B)_4 × "LTL" -> r) .
// $

// - $"lmap" f$ _preprocesses_ the input by reindexing a richer event type $e$ onto
//   the letters $a ∈ Σ$ that a formula observes, so one event stream feeds
//   monitors over different sub-alphabets.
// - $"rmap" g$ _postprocesses_ the verdict — projecting the truth value, or
//   applying the Anticipation look-ahead — as a map on outputs that leaves the
//   dynamics untouched.

// === Composition

// The Mealy machines are themselves the morphisms of a category $bold("Mealy")$:
// objects are alphabets, $bold("Mealy")(a, b) = cal(M)(a, b)$, the identity is the
// copy machine $x |-> (x, "id")$, and series composition threads the state of one
// machine into the next. This composition is exactly the profunctor composition,
// given by the coend

// $
//   (cal(M) ∘ cal(M))(a, c) = integral^(b) cal(M)(a, b) × cal(M)(b, c)
//   quad -> quad cal(M)(a, c),
// $

// and it is how _dependent_ properties are wired: when $ψ$ is evaluated on the
// verdict stream of $φ$, the monitor is the composite $m_φ ⨟ m_ψ$, drawn as the
// block diagram

// #align(center, diagram(
//   spacing: (4.5em, 3em),
//   mbox((0, 0), $m_φ$),
//   mbox((1, 0), $m_ψ$),
//   edge((-1, 0), (0, 0), $Σ$, "->"),
//   edge((0, 0), (1, 0), $bb(B)_4$, "->"),
//   edge((1, 0), (2, 0), $c$, "->"),
//   compbox(((0, 0), (1, 0))),
//   node((0.5, -0.9), text(fill: gray, size: .82em)[$m_φ ⨟ m_ψ$]),
// ))

// where the dashed box is the composite, again a single Mealy machine in
// $cal(M)(Σ, c)$. Operationally the two machines run in lockstep on one tick: an
// event $a ∈ Σ$ enters $m_φ$, which emits a verdict $b ∈ bb(B)_4$ and steps to its
// continuation $m_φ'$; that verdict is fed as the input _letter_ of $m_ψ$, which
// emits the final output $c$ and steps to $m_ψ'$; the composite emits $c$ and
// advances to $m_φ' ⨟ m_ψ'$. Its state is therefore the pair
// $(m_φ, m_ψ)$, and on output maps it is the pipeline
// $partial_(m_φ ⨟ m_ψ) = partial_(m_ψ) ∘ partial_(m_φ)$.

// The intermediate alphabet is the _output_ of $m_φ$, not $Σ$: a dependent monitor
// reads the upstream verdict stream. Concretely one takes $m_φ : cal(M)(Σ, bb(B)_4)$
// — the verdict stream of $φ$, obtained from its full monitor by `rmap` $pi_1$ to
// drop the residual formula — and a meta-property $m_ψ : cal(M)(bb(B)_4, c)$ over
// that stream, e.g. _"$φ$'s verdict has stabilised to $⊤ₚ$"_. Because the composite
// is itself an element of $cal(M)(Σ, c)$, it may be re-typed by `lmap`/`rmap` or
// composed again: the construction is closed.

// $bold("Mealy")$ is moreover monoidal under the product of alphabets, with the
// parallel product $cal(M)(a, b) × cal(M)(c, d) -> cal(M)(a × c, b × d)$.
// Precomposing the parallel of two monitors with the diagonal
// $Delta : Σ -> Σ × Σ$ (that is, $"lmap" Delta$) broadcasts a single event to both
// and pairs their verdicts, $lr(chevron.l m_φ, m_ψ chevron.r) : cal(M)(Σ, (bb(B)_4 ×
//     "LTL")^2)$, with output map

// #align(center, diagram(
//   spacing: (4em, 2.4em),
//   node((0, 0), $Delta$),
//   mbox((1, -1), $m_φ$),
//   mbox((1, 1), $m_ψ$),
//   node((2, 0), $(bb(B)_4 × "LTL")^2$),
//   edge((-1, 0), (0, 0), $Σ$, "->"),
//   edge((0, 0), (1, -1), $Σ$, "->"),
//   edge((0, 0), (1, 1), $Σ$, "->"),
//   edge((1, -1), (2, 0), "->"),
//   edge((1, 1), (2, 0), "->"),
//   compbox(((1, -1), (1, 1))),
//   node((1, -1.8), text(fill: gray, size: .82em)[$lr(chevron.l m_φ\, m_ψ chevron.r)$]),
// ))

// This shared-input fan-out underlies a `monitor` assembled from many formulae:
// every event reaches every declared machine, as described in the overview.

#bibliography("refs.bib")
