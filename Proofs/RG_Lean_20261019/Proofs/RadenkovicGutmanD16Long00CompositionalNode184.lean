/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode030
import Proofs.RadenkovicGutmanD16Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[16],[0]],[[0,0],[0]],[[256,0],[0]],[[0,0],[0]],[[1712,0],[0]],[[0,0],[0]],[[6208,0],[0]],[[0,0],[0]],[[13248,0],[0]],[[0,0],[0]],[[16896,16],[16]],[[0,0],[0]],[[12464,112],[112]],[[0,0],[0]],[[4800,256],[256]],[[0,0],[0]],[[720,208],[208]],[[0,0],[0]],[[0,48],[48]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
