/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode065
import Proofs.RadenkovicGutmanD27Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[27],[0]],[[0,0],[0]],[[432,0],[0]],[[0,0],[0]],[[2889,0],[0]],[[0,0],[0]],[[10476,0],[0]],[[0,0],[0]],[[22356,0],[0]],[[0,0],[0]],[[28512,27],[27]],[[0,0],[0]],[[21033,189],[189]],[[0,0],[0]],[[8100,432],[432]],[[0,0],[0]],[[1215,351],[351]],[[0,0],[0]],[[0,81],[81]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
