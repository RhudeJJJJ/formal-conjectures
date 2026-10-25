/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode045
import Proofs.RadenkovicGutmanD7Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,7]],[[0,0],[0,0]],[[-63,105],[105,2]],[[0,0],[0]],[[759,368],[368]],[[0,0],[0]],[[6467,426],[426]],[[0,0],[0]],[[18548,198],[198]],[[0,0],[0]],[[27516,37],[37]],[[0,0],[0]],[[23772,2],[2]],[[0]],[[12437]],[[0]],[[3928]],[[0]],[[713]],[[0]],[[65]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
