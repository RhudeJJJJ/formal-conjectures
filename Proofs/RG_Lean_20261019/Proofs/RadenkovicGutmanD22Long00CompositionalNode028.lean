/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode024
import Proofs.RadenkovicGutmanD22Long00CompositionalNode027
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e028 : NestedArithmetic.Expr 3 := .plus e024 e027
noncomputable def p028 : NestedHorner.Poly 3 := [[[],[]],[[0,3],[3]],[[0,0],[0]],[[54,13],[13]],[[0,0],[0]],[[378,16],[16]],[[0,0],[0]],[[1044,7],[7]],[[0,0],[0]],[[1514,1],[1]],[[0]],[[1272]],[[0]],[[638]],[[0]],[[188]],[[0]],[[30]],[[0]],[[2]]]
theorem step028 : p028=NestedHorner.add p024 p027 := by decide +kernel
#print axioms step028
theorem h028 : NestedArithmetic.compile e028=p028 := StagedExprCompile.compile_plus e028 e024 e027 p024 p027 p028 rfl h024 h027 step028
#print axioms h028
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
