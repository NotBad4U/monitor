#import "common.typ": *

#show ref: theoretic.show-ref      // this is necessary for references to theorems to work
#show ref: theoretic.show-ref      // this is necessary for references to theorems to work

#set document(title: [Mealy: a #fltl4 monitor])


#show heading.where(level: 1): set heading(numbering: "1")
#show figure.caption: set align(left) //caption left for Figure

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

#include "intro.typ"
#include "preliminaries.typ"
#include "fltl4.typ"
#include "enhanced-m4.typ"
#include "metric-fltl4.typ"
#include "development.typ"

#bibliography("refs.bib")
