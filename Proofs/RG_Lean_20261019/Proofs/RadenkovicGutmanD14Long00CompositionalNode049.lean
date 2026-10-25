/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode045
import Proofs.RadenkovicGutmanD14Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,14]],[[0,0],[0,0]],[[-126,210],[210,2]],[[0,0],[0]],[[1536,718],[718]],[[0,0],[0]],[[12928,804],[804]],[[0,0],[0]],[[36762,352],[352]],[[0,0],[0]],[[54004,58],[58]],[[0,0],[0]],[[46032,2],[2]],[[0]],[[23602]],[[0]],[[7218]],[[0]],[[1238]],[[0]],[[100]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
