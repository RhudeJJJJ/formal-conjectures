/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode017
import Proofs.RadenkovicGutmanD2Long00CompositionalNode156
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e210 : NestedArithmetic.Expr 3 := .times e017 e156
noncomputable def p210 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[30,0],[0,0]],[[0,0],[0,0]],[[188,0],[0,0]],[[0,0],[0,0]],[[638,0],[0,0]],[[0,0],[0,0]],[[1272,0],[0,0]],[[0,0],[0,0]],[[1512,2],[2,0]],[[0,0],[0,0]],[[1028,16],[16,0]],[[0,0],[0,0]],[[334,44],[44,0]],[[0,0],[0,0]],[[6,48],[48,0]],[[0,0],[0,0]],[[-18,18],[18,0]],[[0],[0,0]],[[0],[0,2]]]
theorem step210 : p210=NestedArithmetic.mul p017 p156 := by decide +kernel
#print axioms step210
theorem h210 : NestedArithmetic.compile e210=p210 := StagedExprCompile.compile_times e210 e017 e156 p017 p156 p210 rfl h017 h156 step210
#print axioms h210
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
