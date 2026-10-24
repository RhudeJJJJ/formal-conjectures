/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode029
import Proofs.RadenkovicGutmanD2Long00CompositionalNode030
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e031 : NestedArithmetic.Expr 3 := .plus e029 e030
noncomputable def p031 : NestedHorner.Poly 3 := [[[],[0,1]],[[0,0],[0]],[[-9,9],[9]],[[0,0],[0]],[[3,24],[24]],[[0,0],[0]],[[167,22],[22]],[[0,0],[0]],[[514,8],[8]],[[0,0],[0]],[[756,1],[1]],[[0]],[[636]],[[0]],[[319]],[[0]],[[94]],[[0]],[[15]],[[0]],[[1]]]
theorem step031 : p031=NestedHorner.add p029 p030 := by decide +kernel
#print axioms step031
theorem h031 : NestedArithmetic.compile e031=p031 := StagedExprCompile.compile_plus e031 e029 e030 p029 p030 p031 rfl h029 h030 step031
#print axioms h031
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
