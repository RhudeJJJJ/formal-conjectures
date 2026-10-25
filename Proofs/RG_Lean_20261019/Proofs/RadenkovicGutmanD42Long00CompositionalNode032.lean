/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode029
import Proofs.RadenkovicGutmanD42Long00CompositionalNode031
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e032 : NestedArithmetic.Expr 3 := .plus e029 e031
noncomputable def p032 : NestedHorner.Poly 3 := [[[],[0,1]],[[0,0],[0]],[[-9,9],[9]],[[0,0],[0]],[[3,24],[24]],[[0,0],[0]],[[167,22],[22]],[[0,0],[0]],[[514,8],[8]],[[0,0],[0]],[[756,1],[1]],[[0]],[[636]],[[0]],[[319]],[[0]],[[94]],[[0]],[[15]],[[0]],[[1]]]
theorem step032 : p032=NestedHorner.add p029 p031 := by decide +kernel
#print axioms step032
theorem h032 : NestedArithmetic.compile e032=p032 := StagedExprCompile.compile_plus e032 e029 e031 p029 p031 p032 rfl h029 h031 step032
#print axioms h032
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
