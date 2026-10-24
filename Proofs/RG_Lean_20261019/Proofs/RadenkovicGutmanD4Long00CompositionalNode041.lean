/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e009 e028
noncomputable def p041 : NestedHorner.Poly 3 := [[[0],[0]],[[0,12],[12]],[[0,0],[0]],[[216,52],[52]],[[0,0],[0]],[[1512,64],[64]],[[0,0],[0]],[[4176,28],[28]],[[0,0],[0]],[[6056,4],[4]],[[0]],[[5088]],[[0]],[[2552]],[[0]],[[752]],[[0]],[[120]],[[0]],[[8]]]
theorem step041 : p041=NestedArithmetic.mul p009 p028 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e009 e028 p009 p028 p041 rfl h009 h028 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
