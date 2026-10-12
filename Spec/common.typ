// Shared imports and definitions, imported by every chapter with
//   #import "common.typ": *
// Set/show rules live in main.typ, since they only apply where they are written.

#import "@preview/mmdr:0.2.2": mermaid
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/codly:1.3.0"
#import "@preview/acrostiche:0.7.0": *
#import "@preview/theoretic:0.4.0"
#import "@preview/xarrow:0.4.0": xarrow, xarrowSquiggly, xarrowTwoHead
#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/dashy-todo:0.1.3": todo
#import "@preview/mannot:0.4.0"

#import theoretic.presets.basic: * // this will automatically load predefined styled environments

#import "@preview/cetz:0.5.2"

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

// ---------- palette ----------
#let cteal = rgb("#1D9E75")
#let ctealD = rgb("#0F6E56")
#let cpurpD = rgb("#EF9F27")
#let cpurpDD = rgb("#B26E0A")
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
#let until = $class("binary", bold("U"))$ // infix until, spaced as a binary operator
#let release = $class("binary", bold("R"))$ // infix release, spaced as a binary operator

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
