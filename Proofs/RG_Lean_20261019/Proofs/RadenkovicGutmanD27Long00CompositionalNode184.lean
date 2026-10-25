/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode030
import Proofs.RadenkovicGutmanD27Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[27],[0]],[[0,0],[0]],[[432,0],[0]],[[0,0],[0]],[[2889,0],[0]],[[0,0],[0]],[[10476,0],[0]],[[0,0],[0]],[[22356,0],[0]],[[0,0],[0]],[[28512,27],[27]],[[0,0],[0]],[[21033,189],[189]],[[0,0],[0]],[[8100,432],[432]],[[0,0],[0]],[[1215,351],[351]],[[0,0],[0]],[[0,81],[81]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
