/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode191
import Proofs.RadenkovicGutmanD2Long00CompositionalNode168
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e168
noncomputable def p192 : NestedHorner.Poly 3 := [[[8],[0]],[[0,0],[0]],[[120,0],[0]],[[0,0],[0]],[[752,0],[0]],[[0,0],[0]],[[2552,0],[0]],[[0,0],[0]],[[5088,0],[0]],[[0,0],[0]],[[6056,4],[4]],[[0,0],[0]],[[4176,28],[28]],[[0,0],[0]],[[1512,64],[64]],[[0,0],[0]],[[216,52],[52]],[[0,0],[0]],[[0,12],[12]]]
theorem step192 : p192=NestedArithmetic.mul p191 p168 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e168 p191 p168 p192 rfl h191 h168 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
