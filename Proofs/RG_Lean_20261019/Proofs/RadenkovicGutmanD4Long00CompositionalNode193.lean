/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode192
import Proofs.RadenkovicGutmanD4Long00CompositionalNode169
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e169
noncomputable def p193 : NestedHorner.Poly 3 := [[[16],[0]],[[0,0],[0]],[[240,0],[0]],[[0,0],[0]],[[1504,0],[0]],[[0,0],[0]],[[5104,0],[0]],[[0,0],[0]],[[10176,0],[0]],[[0,0],[0]],[[12112,8],[8]],[[0,0],[0]],[[8352,56],[56]],[[0,0],[0]],[[3024,128],[128]],[[0,0],[0]],[[432,104],[104]],[[0,0],[0]],[[0,24],[24]]]
theorem step193 : p193=NestedArithmetic.mul p192 p169 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e169 p192 p169 p193 rfl h192 h169 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
