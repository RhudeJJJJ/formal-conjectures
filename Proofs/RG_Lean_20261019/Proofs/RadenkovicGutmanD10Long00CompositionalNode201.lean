/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode198
import Proofs.RadenkovicGutmanD10Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[84,0],[0,0]],[[0,0],[0,0]],[[994,0],[0,0]],[[0,0],[0,0]],[[5662,0],[0,0]],[[0,0],[0,0]],[[18222,0],[0,0]],[[0,0],[0,0]],[[35088,2],[2,0]],[[0,0],[0,0]],[[40700,46],[46,0]],[[0,0],[0,0]],[[27414,264],[264,0]],[[0,0],[0,0]],[[9548,588],[588,0]],[[0,0],[0,0]],[[1128,518],[518,0]],[[0,0],[0,0]],[[-90,150],[150,2]],[[0],[0,0]],[[0],[0,10]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
