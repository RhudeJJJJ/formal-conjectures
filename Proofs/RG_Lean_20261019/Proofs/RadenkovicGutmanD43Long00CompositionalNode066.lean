/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode065
import Proofs.RadenkovicGutmanD43Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-43]],[[0,0],[0,0]],[[-387,-645],[-645,-2]],[[0,0],[0]],[[-10725,-2168],[-2168]],[[0,0],[0]],[[-56089,-2370],[-2370]],[[0,0],[0]],[[-129878,-990],[-990]],[[0,0],[0]],[[-164368,-145],[-145]],[[0,0],[0]],[[-123344,-2],[-2]],[[0]],[[-56323]],[[0]],[[-15410]],[[0]],[[-2351]],[[0]],[[-163]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
