// The formulas of the spec, and nothing else.
//
// Each formula is a variable defined next to its prose in a chapter file and only
// imported here, so editing a chapter updates this sheet. To add a formula, define
// it with a hyphenated name (a plain one like `flat` or `kappa` would shadow the
// math symbol in the whole chapter), then import it and give it an `entry` below.

#import "common.typ": *
#import "preliminaries.typ": b2-def, b2-order, ltl-syntax, ltl-abbrev, ltl-sem, ltl-sem-sig, fltl-sem
#import "fltl4.typ": (
  b4-def, b4-order, b4-compl, b4-not-boolean-top, b4-not-boolean-bot,
  fltl4-syntax, fltl4-sem, fltl4-sem-sig,
  mealy-tuple, mealy-delta, m4-tuple, m4-delta, m4-correct,
)
#import "enhanced-m4.typ": (
  mealy-coalg-map, mealy-coalg, mealy-hom,
  profunctor-def, mealy-functor, mealy-nat, mly-type, mly-obj, mly-mor, mly-actions, m4-actions, mly-comp,
  free-monad, free-ctors, futu-coalg, futu-resume, futu-def, futu-flat, futu-universal, dec-def, residual-lemma,
  m4k-final-verdict, m4k-kappa, m4k-step-type, m4k-step, m4k-plan, m4k-def,
  m4-enhanced, m4-enhanced-coalg,
)
#import "metric-fltl4.typ": (
  mfltl4, tfptl4,
  timed-word, timed-word-mono,
  mfltl4-syntax, mfltl4-abbrev, mfltl4-sem, mfltl4-sem-sig,
  tfptl4-syntax, tfptl4-sem, tfptl4-sem-sig, clock-valuation,
)

#set document(title: [Mealy: #fltl4 formula sheet])
#set page(numbering: "1", number-align: center + bottom)
#set text(size: 10pt)

#title()

// an inline formula is set as a display one, the rest is shown as it is
#let display(f) = if f.func() == math.equation and not f.block {
  math.equation(block: true, f.body)
} else {
  f
}

// several short formulas on a single display line
#let side(..fs) = math.equation(block: true, fs.pos().map(f => f.body).join(h(3em)))

// one item of the sheet: a rubric followed by its formulas
#let entry(name, ..formulas) = block(breakable: false, width: 100%, above: 1.6em, {
  text(weight: "bold", fill: ctealD, name)
  for f in formulas.pos() { display(f) }
})

= Preliminaries

#entry([Truth domain $bb(B)_2$], side(b2-def, b2-order))

== LTL

#entry([Syntax], ltl-syntax)
#entry([Abbreviations], ltl-abbrev)
#entry([Semantics], ltl-sem-sig, ltl-sem)

== FLTL

#entry([Semantics (other clauses as for LTL)], fltl-sem)

= The logic #fltl4

#entry([Truth domain $bb(B)_4$], side(b4-def, b4-order), b4-compl)
#entry([$bb(B)_4$ is not Boolean], side(b4-not-boolean-top, b4-not-boolean-bot))
#entry([Syntax], fltl4-syntax)
#entry([Semantics], fltl4-sem-sig, fltl4-sem)

== Monitor as a Mealy machine

#entry([Mealy machine], side(mealy-tuple, mealy-delta))
#entry([Monitor #M4], m4-tuple, m4-delta)
#entry([Correctness], m4-correct)

= Enhanced #M4

#entry([Mealy machine as an $frak(M)$-coalgebra], mealy-coalg-map, mealy-coalg)
#entry([Mealy homomorphism], mealy-hom)

== Profunctor

#entry([Profunctor], profunctor-def)
#entry([Mealy functor], mealy-functor, mealy-nat)
#entry([Mealy profunctor $Mly$], mly-type, mly-obj, mly-mor)
#entry([Actions], mly-actions, m4-actions)
#entry([Composition], mly-comp)

== Anticipation as a futumorphism

#entry([Plans $Fre$], free-monad, free-ctors)
#entry([$frak(M)$-futumorphism], futu-coalg, futu-resume, futu-def)
#entry([Flattening and universal property], futu-flat, futu-universal)
#entry([Decided residual], dec-def, residual-lemma)
#entry(
  [Anticipating monitor $cal(M)_4^(phi, k)$],
  m4k-final-verdict, m4k-kappa, m4k-step-type, m4k-step, m4k-plan, m4k-def,
)

== Final picture

#entry([Enhanced monitor], m4-enhanced, m4-enhanced-coalg)

= Timed RV-LTL

#entry([Timed word], timed-word, timed-word-mono)

== Metric RV-LTL: #mfltl4

#entry([Syntax], mfltl4-syntax)
#entry([Abbreviations], mfltl4-abbrev)
#entry([Semantics], mfltl4-sem-sig, mfltl4-sem)

== Timed Propositional RV-LTL: #tfptl4

#entry([Syntax], tfptl4-syntax)
#entry([Clock valuation], clock-valuation)
#entry([Semantics], tfptl4-sem-sig, tfptl4-sem)
