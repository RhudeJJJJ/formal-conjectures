/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode075
import Proofs.RadenkovicGutmanD22Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,484]],[[0,0],[0,0,0],[0,0]],[[0,0,4356],[0,8712,8712],[4356,8712]],[[0,0,0],[0,0,0],[0,0]],[[-39204,143748,76956],[143748,232320,23232],[76956,23232]],[[0,0,0],[0,0,0],[0,0]],[[496584,2313036,337348],[2313036,1092872,21296],[337348,21296]],[[0,0,0],[0,0,0],[0,0]],[[13995828,13325004,692120],[13325004,2325136,7744],[692120,7744]],[[0,0,0],[0,0,0],[0,0]],[[107857464,41017064,795696],[41017064,2752992,968],[795696,968]],[[0,0,0],[0,0],[0]],[[448783676,78544972,549824],[78544972,1957296],[549824]],[[0,0,0],[0,0],[0]],[[1203369200,100830268,232804],[100830268,852808],[232804]],[[0,0,0],[0,0],[0]],[[2258193960,90304720,59048],[90304720,222640],[59048]],[[0,0,0],[0,0],[0]],[[3106030312,57562604,8228],[57562604,31944],[8228]],[[0,0,0],[0,0],[0]],[[3219650280,26260388,484],[26260388,1936],[484]],[[0,0],[0]],[[2557388240,8506784],[8506784]],[[0,0],[0]],[[1570352520,1909380],[1909380]],[[0,0],[0]],[[747265992,282172],[282172]],[[0,0],[0]],[[274572716,24684],[24684]],[[0,0],[0]],[[77089584,968],[968]],[[0]],[[16218840]],[[0]],[[2473240]],[[0]],[[257972]],[[0]],[[16456]],[[0]],[[484]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
