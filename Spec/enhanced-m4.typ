#import "common.typ": *

= Enhanced #M4  <sec-m4>

In the previous section, we showed how to derive a monitor for an #fltl4 from a Mealy machine. However, this machine does not tackle all the problems, such as mechanising the Anticipation maxim. Furthermore, a system is rarely defined by a single property; it can be a composition of multiple temporal properties, and for now, we have not defined how to compose monitors. In this section, we present our approach to extending Mealy machines to solve these problems.

First, we present the coalgebraic aspect of Mealy machine @mealy-coalg @bonchi2026effectfulmealymachines. Let $A$ be a finite set and let $B$ be a (possibly infinite) meet-semilattice. A Mealy machine (S, $f$) with inputs in A and outputs in B consists of a set of states $S$ together with a function:
$
  f:S -> (B times S)^A
$
Such a map $f$ is equivalent to the _uncurried_ map between cartesian product $chevron.l "out", "next"chevron.r: A times S -> B times S$.
In coalgebraic terms, a Mealy machine $cal(M)(S, f)$ is  a coalgebra of the functor $frak(M): "Set" -> "Set"$ defined, for any set X, as $frak(M)(X) = (B times X)^A$. Throughout this subsection $A$ and $B$ stay fixed; @def:mealy-prof[-] releases them and turns $frak(M)$ into a family $frak(M)_(A,B)$ indexed by the two alphabets.

#definition(label: <def:mealy-coalg>)[
  A $frak(M)$-_coalgebra_ is a pair $(C, gamma)$, where $C$ is a set (of states) and $gamma: C -> frak(M)(C)$ is a (transition) function.
]

We adopt the notation $s tr(a, b) s'$ to denotes the (transition) function result $f(s)(a) = ⟨b, s'⟩$.

#example([$frak(M)$-coalgebra of $bold(F) q$ and $bold(G) p$], label: <ex:coalg>)[
  Let $bold("AP") = {p, q}$ and $Σ = 2^bold("AP")$, and take $A = Σ$, $B = bb(B)_4$. The
  #M4 of @def:m4[-] is the $frak(M)$-coalgebra $(C, gamma)$ whose carrier $C$ is the set of
  residual formulae reachable from the property and whose transition is
  $gamma(phi)(a) = delta_4(a, phi)$. The alphabet $Σ$ is not part of the pair: it sits in
  the functor, as the exponent of $frak(M)(C) = (bb(B)_4 times C)^Σ$. Unfolding @def:m4[-] on
  $bold(F) q = q or bold(X) bold(F) q$ and $bold(G) p = p and overline(bold(X)) bold(G) p$
  gives, for every $a in Σ$,
  $
    gamma(bold(F) q)(a) & = cases(
                            ⟨top, "true"⟩ & "if " q in a,
                            ⟨bot^p, bold(F) q⟩,
                          ) \
    gamma(bold(G) p)(a) & = cases(
                            ⟨top^p, bold(G) p⟩ "if " p in a,
                            ⟨bot, "false"⟩,
                          )
  $
  so each property needs only two states, $C = {bold(F) q, "true"}$ and
  $C = {bold(G) p, "false"}$ respectively. On the trace $u = {p}{p}{q}$ the two runs are
  $
    bold(F) q & tr({p}, bot^p) bold(F) q tr({p}, bot^p) bold(F) q tr({q}, top) "true" \
    bold(G) p & tr({p}, top^p) bold(G) p tr({p}, top^p) bold(G) p tr({q}, bot) "false"
  $
  emitting $bot^p bot^p top$ and $top^p top^p bot$,
  that is $sem(u tack.rr bold(F) q) = top$ and $sem(u tack.rr bold(G) p) = bot$ @rv-ltl.
  Both verdicts are definitive, and this is what settles the infinite words:
  $semw({p}({p}{q})^ω tack.rr bold(F) q) = top$ and
  $semw({p}({p}{q})^ω tack.rr bold(G) p) = bot$. Note that the machine reaches the
  definitive verdict only on the third letter, one layer at a time and this is the limitation
  the anticipating monitor removes.
]

#proposition("Mealy homomorphism", label: <def:mealy-hom>)[
  A homomorphism from a Mealy machine $(S, f)$ to a Mealy machine $(T, g)$ is a function $h: S -> T$ preserving initial outputs and next states:
  $
    g compose h = frak(M)(h) compose f, quad "where " frak(M)(h) = ("id"_B times h)^A
  $
]

== #M4 compositions and pre-post treatments with Profunctor

In @def:mealy[-], the set of input and output language are fixed and without side-effect.
A potential property would be to make them parametric or dynamically computed.
Both intentions are captured by reading a Mealy machine as an element of a _profunctor_
@benabou2000distributors, contravariant in the input alphabet (the pre-treatment) and covariant in
the output alphabet (the post-treatment).

#definition([Mealy profunctor $Mly$], label: <def:mealy-prof>)[
  A _profunctor_ $P : cal(C) arrow.r.not cal(D)$ is a functor
  $P : cal(D)^"op" times cal(C) -> "Set"$ @benabou2000distributors. An element of $P(d, c)$ is
  a _heteromorphism_ $d -> c$ (not a morphism of $cal(C)$ nor of $cal(D)$).
  For $f : d -> d' in cal(D)$, $g : c -> c' in cal(C)$ and $x in P(d', c)$, the two actions
  are written $x compose f in P(d, c)$ and $g compose x in P(d', c')$.

  In @def:mealy-coalg[-] the two alphabets were fixed. Releasing them turns $frak(M)$ into a
  family of endofunctors indexed by them,
  $
    frak(M) : "Set"^"op" times "Set" -> ["Set", "Set"], quad
    frak(M)_(A,B)(X) = (B times X)^A
  $
  contravariant in $A$ and covariant in $B$: a pre-treatment $f : A' -> A$ and a post-treatment
  $g : B -> B'$ induce the natural transformation
  $
    frak(M)_(f,g) : frak(M)_(A,B) => frak(M)_(A',B'), quad
    (frak(M)_(f,g))_X (h) = (g times "id"_X) compose h compose f
  $
  The Mealy profunctor is this family followed by the final-coalgebra operator $nu$,
  $
    Mly : "Set"^"op" times "Set" -> "Set"
  $
  a functor with the usual two components:

  - on _objects_, the set of Mealy behaviours from the input alphabet $A$ to the output
    alphabet $B$,
    $
      Mly(A, B) := nu frak(M)_(A,B) = nu X. #h(.2em) (B times X)^A
    $
    By finality it carries an isomorphism
    $"out" : Mly(A, B) -> frak(M)_(A,B)(Mly(A, B)) = (B times Mly(A, B))^A$; we write
    $m(a) = ⟨b, m'⟩$ for one unfolding.
  - on _morphisms_, the image of $frak(M)_(f,g)$ under $nu$: post-composing $"out"$ with
    $frak(M)_(f,g)$ turns the set $Mly(A, B)$ into an $frak(M)_(A',B')$-coalgebra, and
    $Mly(f, g)$ is its anamorphism @yang2022fantasticmorphismsthemguide into the final one,
    $
      Mly(f, g) := "ana"(frak(M)_(f,g) compose "out") : Mly(A, B) -> Mly(A', B')
    $
]

#proposition[ The two profunctor actions written above are the degenerate cases $m compose f := Mly(f, "id"_B)(m)$ and
  $g compose m := Mly("id"_A, g)(m)$, which unfold to
  $
    (m compose f)(a') & = ⟨b, m' compose f⟩, quad    & "where" ⟨b, m'⟩ = m(f(a')) \
     (g compose m)(a) & = ⟨g(b), g compose m'⟩, quad &     "where" ⟨b, m'⟩ = m(a)
  $
  so that $m compose f in Mly(A', B)$ and $g compose m in Mly(A, B')$. The semilattice structure
  asked of $B$ in @def:mealy-coalg[-] plays no role here: $Mly$ takes its output alphabet in
  $"Set"$, and $g$ is an arbitrary function.
]

#example([Re-alphabetising the $bold(F) q$ monitor], label: <ex:prof>)[
  Let $m in Mly(Σ, bb(B)_4)$ be the behaviour of the $bold(F) q$ machine unfolded above.
  Take a set $bb(E)$ of program events, each carrying more than the two atoms, and

  - a _pre-treatment_ $f : bb(E) -> Σ$ keeping of an event only which of $p, q$ hold;
  - a _post-treatment_ $g : bb(B)_4 -> bb(B)_2$ collapsing the presumable verdicts,
    $g(top) = g(top^p) = top$ and $g(bot) = g(bot^p) = bot$.

  The two actions of @def:mealy-prof[-] give $m compose f in Mly(bb(E), bb(B)_4)$,
  $g compose m in Mly(Σ, bb(B)_2)$ and $g compose m compose f in Mly(bb(E), bb(B)_2)$, the last one unfolding as
  $
    (g compose m compose f)(e) = ⟨g(b), g compose m' compose f⟩, quad "where " ⟨b, m'⟩ = m(f(e)) .
  $
  On events $e_1 e_2 e_3$ with $f(e_1) = f(e_2) = {p}$ and $f(e_3) = {q}$, the run of
  $g compose m compose f$ is
  $
    bold(F) q tr(e_1, bot) bold(F) q tr(e_2, bot) bold(F) q tr(e_3, top) "true"
  $
  the same states as above, read through $g$: the stream $bot^p bot^p top$ has become
  $bot bot top$. By @def:actions[-] neither action touches $S$ or $s_0$: the four-valued monitor over $Σ$ and its two-valued reading over $bb(E)$ are one machine, wired differently.
]

The two actions of @def:mealy-prof[-] _are_ the pre- and the post-treatment of a machine. Both
keep $S$ and $s_0$ and only rewire the transition (@fig-prof-actions), which is why neither can
enlarge #M4.

#definition([Actions on #M4], label: <def:actions>)[
  On a machine presentation, the right action $m compose f in Mly(A', B)$ (pre-treatment) and the left
  action $g compose m in Mly(A, B')$ (post-treatment) keep $S$ and $s_0$ and rewire the transition:
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

#figure(
  placement: top,
  // ── the two actions are pure boxes on either side of m ──────────
  diagram(
    spacing: (2.9em, 1.4em),
    node-outset: 1pt,
    node((0, 0), elbl($A'$, caxis), name: <pa>),
    mbox((1, 0), text(size: .92em, $f$), name: <pf>),
    sbox((2, 0), text(size: .92em, $m$), cteal, name: <pm>),
    mbox((3, 0), text(size: .92em, $g$), name: <pg>),
    node((4, 0), elbl($B'$, caxis), name: <pb>),
    edge(<pa>, <pf>, "->", stroke: cgray + .6pt),
    edge(<pf>, <pm>, elbl($A$, caxis), "->", stroke: cgray + .6pt),
    edge(<pm>, <pg>, elbl($B$, caxis), "->", stroke: cgray + .6pt),
    edge(<pg>, <pb>, "->", stroke: cgray + .6pt),
    compbox((<pf>, <pm>, <pg>)),
    node((2, 1.25), dtext(size: .76em)[$g compose m compose f$]),
  ),
  caption: [
    The two actions of @def:mealy-prof[-], read as wiring: pre- and post-treatment are boxes on
    either side of $m$, and the state space $S$ of $m$ is untouched.
  ],
) <fig-prof-actions>

#definition([Mealy composition], label: <def:mly-comp>)[
  Profunctors compose by tracing out the middle object with a _coend_ @coend. We write that
  composition $seq$, in diagrammatic order, so that $P seq Q$ is "$P$ first, then $Q$".
  Composing $Mly$ with itself over a middle alphabet $B$ is given by:
  $
    (Mly seq Mly)(A, C) = integral^B Mly(A, B) times Mly(B, C).
  $
  A representative is a pair $(m, n)$ of heteromorphisms $m : A arrow.r.not B$ and
  $n : B arrow.r.not C$, that is $m in Mly(A, B)$ and $n in Mly(B, C)$ for some $B$, and
  the coend identifies $(g compose m, n)$ with $(m, n compose g)$ for every $g : B -> B'$, $m in Mly(A, B)$ and
  $n in Mly(B', C)$. The same symbol carries the induced operation on heteromorphisms,
  $m seq n in Mly(A, C)$ (@fig-prof-comp): composing the two profunctors and composing two
  machines are one operation read at two levels.
]

#figure(
  stack(
    dir: ttb,
    spacing: 2.4em,

    // ── (a) composition hides the middle alphabet and the state ─────────
    diagram(
      spacing: (3.4em, 1.4em),
      node-outset: 1pt,
      node((0, 0), elbl($A$, caxis), name: <sa>),
      sbox((1, 0), text(size: .92em, $m$), cteal, name: <sm>),
      sbox((2, 0), text(size: .92em, $n$), cpurpD, name: <sn>),
      node((3, 0), elbl($C$, caxis), name: <sc>),
      edge(<sa>, <sm>, "->", stroke: cgray + .6pt),
      edge(<sm>, <sn>, elbl($B$, caxis), "->", stroke: cgray + .6pt),
      edge(<sn>, <sc>, "->", stroke: cgray + .6pt),
      compbox((<sm>, <sn>)),
      node((1.5, 1.25), dtext(size: .76em)[$m seq n$ — $B$ and $S times T$ are both inside the box]),
    ),

    // ── (b) the coend identification: g slides across the junction ──────
    diagram(
      spacing: (3.3em, 1.4em),
      node-outset: 1pt,
      // left wiring: (g m, n)
      sbox((0, 0), text(size: .92em, $m$), cteal, name: <lm>),
      mbox((1, 0), text(size: .92em, $g$), name: <lg>),
      sbox((2, 0), text(size: .92em, $n$), cpurpD, name: <ln>),
      edge(<lm>, <lg>, elbl($B$, caxis), "->", stroke: cgray + .6pt),
      edge(<lg>, <ln>, elbl($B'$, caxis), "->", stroke: cgray + .6pt),
      compbox((<lm>, <lg>), inset: 9pt),
      node((.5, 1.35), dtext(fill: ctealD, size: .76em)[$(g compose m, n)$]),

      node((3, 0), text(size: 1.1em, fill: cgray, $tilde$)),

      // right wiring: (m, n g)
      sbox((4, 0), text(size: .92em, $m$), cteal, name: <rm>),
      mbox((5, 0), text(size: .92em, $g$), name: <rg>),
      sbox((6, 0), text(size: .92em, $n$), cpurpD, name: <rn>),
      edge(<rm>, <rg>, elbl($B$, caxis), "->", stroke: cgray + .6pt),
      edge(<rg>, <rn>, elbl($B'$, caxis), "->", stroke: cgray + .6pt),
      compbox((<rg>, <rn>), inset: 9pt),
      node((5.5, 1.35), dtext(fill: cpurpDD, size: .76em)[$(m, n compose g)$]),
    ),
  ),
  caption: [
    The composition of @def:mly-comp[-], read as wiring: $seq$ hides the middle alphabet $B$ and
    the joint state space, and the coend lets $g$ slide across the junction.
  ],
) <fig-prof-comp>



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
          "futu" & : (S -> frak(M)(Fre space S)) -> S -> Mly(A, B) \
    "futu" gamma & := "ana"(gamma^dagger) compose eta #h(.6em) : #h(.6em) S -> Mly(A, B).
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
    spacing: (8.4em, 4.8em),
    node-outset: 3pt,
    node((0, 0), $S$, name: <ua>),
    node((1, 0), $frak(M)(Fre (S))$, name: <ub>),
    node((0, 1), $Mly(A, B)$, name: <uc>),
    node((1, 1), $frak(M)(Mly(A, B))$, name: <ud>),
    edge(<ua>, <ub>, elbl($gamma$, caxis), "->", stroke: cgray + .6pt),
    edge(
      <ua>,
      <uc>,
      elbl($"futu"(gamma)$, ctealD),
      "-->",
      label-side: right,
      stroke: ctealD + .7pt,
    ),
    edge(<ub>, <ud>, elbl($frak(M)(flat compose Fre (h))$, caxis), "->", stroke: cgray + .6pt),
    edge(<uc>, <ud>, elbl($"out" #h(.25em)$, caxis), "->", stroke: cgray + .6pt),
  ),
  caption: [
    How the anticipating behaviour $"futu" gamma in Mly(A, B)$ is constructed from $gamma$.
  ],
) <fig-futu-square>

#definition([Decided residual], label: <def:decided>)[
  A formula $phi$ is _decided_ on $b in bb(B)_2 subset bb(B)_4$, written $"dec"(phi) = b$, when every
  infinite word agrees on it:
  $
    "dec"(phi) = b quad "iff" quad forall w in Σ^ω. #h(.3em) semw(w tack.rr phi) = b
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
  We write $"plan"_j : #fltl4 -> Fre (#fltl4)$ for the continuation that unfolds $j$ layers:
  $
    "plan"_0 = eta, quad "plan"_(j+1) = "op" compose "step"_("plan"_j) .
  $
  Finally, the anticipating coalgebra and the machine it denotes are then:
  $
                 gamma_4^k & : #fltl4 -> frak(M)(Fre (#fltl4)) \
                 gamma_4^k & := "step"_("plan"_(k-1)) \
    quad cal(M)_4^(phi, k) & := "futu"(gamma_4^k)(phi) in Mly(Σ, bb(B)_4).
  $
]

#example([Anticipation], label: <ex:futu>)[
  Take $phi = bold(G) "true"$. For every $a in Σ$, @def:m4[-] gives
  $
    delta_4(a, bold(G) "true") & equiv delta_4(a, "true" and overline(bold(X)) bold(G) "true") \
                               & equiv (top inter.sq top^p, #h(.3em) "nrm"("true" and bold(G) "true")) \
                               & equiv (top^p, bold(G) "true"),
  $
  so #M4 emits $top^p$ on every letter and never commits, and dually
  $delta_4(a, bold(F) "false") = (bot^p, bold(F) "false")$ emits $bot^p$ forever @rv-ltl.
  Yet every infinite word satisfies $bold(G) "true"$ and none satisfies $bold(F) "false"$,
  so $"dec"(bold(G) "true") = top$ and $"dec"(bold(F) "false") = bot$ and the commit branch
  fires on the _first_ letter:
  $
    "step"_kappa (bold(G) "true")(a) = ⟨top, eta(top)⟩, quad
    "step"_kappa (bold(F) "false")(a) = ⟨bot, eta(bot)⟩ .
  $
  The constant seed is absorbing, so the verdict is repeated forever and never retracted.

  _Lookahead._ The commit branch discards $kappa$, so a plan only does real work on an
  undecided residual. Take $phi = bold(F) q$ and $k = 2$, so
  $gamma_4^2 = "step"_("plan"_1)$ with $"plan"_1 = "op" compose "step"_eta$ and
  $
    "step"_eta (bold(F) q)(a) = cases(
      ⟨top, eta(top)⟩ & "if " q in a #h(.5em) ("dec"("true") = top", commit"),
      ⟨bot^p, eta(bold(F) q)⟩ & "else" #h(1.1em) ("dec"(bold(F) q) = #h(.15em) ?", defer"),
    )
  $
  Reading $a = {p}$ leaves the residual $bold(F) q$ undecided, so $gamma_4^2$ defers and
  answers $gamma_4^2 (bold(F) q)({p}) = ⟨bot^p, "plan"_1 (bold(F) q)⟩$. The successor is no
  longer a bare state but a plan already holding the whole next-letter decision tree, its
  branches ending in seeds: the machine has looked two letters ahead in one move, which is
  what $Fre$ buys and an anamorphism cannot express.
]

#proposition([$cal(M)_4^(phi, k)$ satisfies Anticipation], label: <prop:anticipation>)[
  Let $phi$ be an #fltl4 formula, let $k >= 1$, let $u = u_1 dots u_n in Σ^+$, and let
  $b_n in bb(B)_4$ be the $n$-th output of $cal(M)_4^(phi, k)$ on $u$. Then
  + _(soundness)_ if $b_n in {top, bot}$ then $semw(u w tack.rr phi) = b_n$ for every
    $w in Σ^ω$;
  + _(anticipation)_ conversely, if $semw(u w tack.rr phi) = b$ for every $w in Σ^ω$ and some
    $b in {top, bot}$, then $b_n = b$;
  + _(agreement)_ if no prefix of $u$ has a decided residual, then $b_n = sem(u tack.rr phi)$.
]

== Final picture of Enhanced #M4

#figure(
  placement: top,
  table(
    columns: (auto, 1fr),
    align: (left + top, left + top),
    stroke: none,
    inset: (x: .7em, y: .8em),
    table.hline(stroke: .8pt),
    table.header([*Construction*], [*Contribution:*]),
    table.hline(stroke: .5pt),

    $frak(M)_(A,B)(X) = (B times X)^A$,
    [
      The Mealy functor, whose coalgebras are exactly the Mealy machines: a set of states
      with a map sending each state to one transition layer, namely an output letter and a
      successor for every input letter (@def:mealy-coalg[-]).
    ],

    $Mly(A, B) = nu frak(M)_(A,B)$,
    [
      The Mealy profunctor, contravariant in the input alphabet and covariant in the output
      one, so that both alphabets become parameters (@def:mealy-prof[-]).
    ],

    $Fre (X) = mu Y. #h(.2em) X + frak(M)(Y)$,
    [
      The plans over a set of seeds. A plan is a finite stack of transition layers computed
      in advance, every branch of which ends in a seed to be resumed later
      (@def:free-mealy[-]).
    ],

    table.hline(stroke: .8pt),
  ),
  caption: [The constructions the enhanced monitor is assembled from.],
) <tab-constructions>

The three enhancements (@tab-constructions) are the three stacks of the final monitor that we name $cal(M)_4^(phi, k)$.
Fix a formula $phi$, a horizon $k >= 1$, a pre-treatment $f : A -> Σ$ and a post-treatment
$g : bb(B)_4 -> B$. The enhanced monitor is the profunctor:
$
  cal(M)_4^(phi, k) [f, g] := g compose "futu"(gamma_4^k)(phi) compose f in Mly(A, B)
$
unfolded from the single anticipating coalgebra
$
  gamma_4^k : #fltl4 -> frak(M)_(Σ, bb(B)_4)(Fre (#fltl4))
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

#remark()[
  Setting $k = 1$ and $f = "id"_Σ$, $g = "id"_(bb(B)_4)$ collapses every layer at once and
  returns the #M4 of @def:m4[-]: the enhancements are extensions, not replacements.
]
