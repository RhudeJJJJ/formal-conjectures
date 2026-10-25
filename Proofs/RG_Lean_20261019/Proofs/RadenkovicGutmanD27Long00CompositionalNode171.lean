/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode030
import Proofs.RadenkovicGutmanD27Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[54],[0]],[[0,0],[0]],[[810,0],[0]],[[0,0],[0]],[[5076,0],[0]],[[0,0],[0]],[[17226,0],[0]],[[0,0],[0]],[[34344,0],[0]],[[0,0],[0]],[[40878,27],[27]],[[0,0],[0]],[[28188,189],[189]],[[0,0],[0]],[[10206,432],[432]],[[0,0],[0]],[[1458,351],[351]],[[0,0],[0]],[[0,81],[81]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
