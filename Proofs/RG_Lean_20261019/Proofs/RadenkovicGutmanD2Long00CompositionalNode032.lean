/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode017
import Proofs.RadenkovicGutmanD2Long00CompositionalNode031
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e032 : NestedArithmetic.Expr 3 := .times e017 e031
noncomputable def p032 : NestedHorner.Poly 3 := [[[0],[0,2]],[[0,0],[0]],[[-18,18],[18]],[[0,0],[0]],[[6,48],[48]],[[0,0],[0]],[[334,44],[44]],[[0,0],[0]],[[1028,16],[16]],[[0,0],[0]],[[1512,2],[2]],[[0]],[[1272]],[[0]],[[638]],[[0]],[[188]],[[0]],[[30]],[[0]],[[2]]]
theorem step032 : p032=NestedArithmetic.mul p017 p031 := by decide +kernel
#print axioms step032
theorem h032 : NestedArithmetic.compile e032=p032 := StagedExprCompile.compile_times e032 e017 e031 p017 p031 p032 rfl h017 h031 step032
#print axioms h032
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
