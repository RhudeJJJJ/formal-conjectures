/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode192
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e003
noncomputable def p193 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[8,0],[0]],[[0,0],[0]],[[120,0],[0]],[[0,0],[0]],[[752,0],[0]],[[0,0],[0]],[[2552,0],[0]],[[0,0],[0]],[[5088,0],[0]],[[0,0],[0]],[[6056,4],[4]],[[0,0],[0]],[[4176,28],[28]],[[0,0],[0]],[[1512,64],[64]],[[0,0],[0]],[[216,52],[52]],[[0,0],[0]],[[0,12],[12]]]
theorem step193 : p193=NestedArithmetic.mul p192 p003 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e003 p192 p003 p193 rfl h192 h003 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
