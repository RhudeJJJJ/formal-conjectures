/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode030
import Proofs.RadenkovicGutmanD11Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,11]],[[0,0],[0]],[[99,99],[99]],[[0,0],[0]],[[1749,264],[264]],[[0,0],[0]],[[7667,242],[242]],[[0,0],[0]],[[15730,88],[88]],[[0,0],[0]],[[18084,11],[11]],[[0]],[[12496]],[[0]],[[5291]],[[0]],[[1342]],[[0]],[[187]],[[0]],[[11]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
