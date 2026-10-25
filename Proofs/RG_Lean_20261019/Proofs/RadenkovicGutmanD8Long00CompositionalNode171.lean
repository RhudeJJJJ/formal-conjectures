/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode030
import Proofs.RadenkovicGutmanD8Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[16],[0]],[[0,0],[0]],[[240,0],[0]],[[0,0],[0]],[[1504,0],[0]],[[0,0],[0]],[[5104,0],[0]],[[0,0],[0]],[[10176,0],[0]],[[0,0],[0]],[[12112,8],[8]],[[0,0],[0]],[[8352,56],[56]],[[0,0],[0]],[[3024,128],[128]],[[0,0],[0]],[[432,104],[104]],[[0,0],[0]],[[0,24],[24]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
