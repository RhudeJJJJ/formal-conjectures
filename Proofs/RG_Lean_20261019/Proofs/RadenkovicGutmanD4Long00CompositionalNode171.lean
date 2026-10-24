/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode170
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e170 e003
noncomputable def p171 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[8,0],[0]],[[0,0],[0]],[[120,0],[0]],[[0,0],[0]],[[752,0],[0]],[[0,0],[0]],[[2552,0],[0]],[[0,0],[0]],[[5088,0],[0]],[[0,0],[0]],[[6056,4],[4]],[[0,0],[0]],[[4176,28],[28]],[[0,0],[0]],[[1512,64],[64]],[[0,0],[0]],[[216,52],[52]],[[0,0],[0]],[[0,12],[12]]]
theorem step171 : p171=NestedArithmetic.mul p170 p003 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e170 e003 p170 p003 p171 rfl h170 h003 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
