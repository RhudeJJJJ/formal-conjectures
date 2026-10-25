/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode171
import Proofs.RadenkovicGutmanD8Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[16,0],[0]],[[0,0],[0]],[[240,0],[0]],[[0,0],[0]],[[1504,0],[0]],[[0,0],[0]],[[5104,0],[0]],[[0,0],[0]],[[10176,0],[0]],[[0,0],[0]],[[12112,8],[8]],[[0,0],[0]],[[8352,56],[56]],[[0,0],[0]],[[3024,128],[128]],[[0,0],[0]],[[432,104],[104]],[[0,0],[0]],[[0,24],[24]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
