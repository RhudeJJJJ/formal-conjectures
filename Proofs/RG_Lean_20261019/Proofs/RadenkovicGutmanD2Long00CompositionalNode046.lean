/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode045
import Proofs.RadenkovicGutmanD2Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e046 : NestedArithmetic.Expr 3 := .times e045 e028
noncomputable def p046 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,12],[12]],[[0,0],[0]],[[216,52],[52]],[[0,0],[0]],[[1512,64],[64]],[[0,0],[0]],[[4176,28],[28]],[[0,0],[0]],[[6056,4],[4]],[[0]],[[5088]],[[0]],[[2552]],[[0]],[[752]],[[0]],[[120]],[[0]],[[8]]]
theorem step046 : p046=NestedArithmetic.mul p045 p028 := by decide +kernel
#print axioms step046
theorem h046 : NestedArithmetic.compile e046=p046 := StagedExprCompile.compile_times e046 e045 e028 p045 p028 p046 rfl h045 h028 step046
#print axioms h046
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
