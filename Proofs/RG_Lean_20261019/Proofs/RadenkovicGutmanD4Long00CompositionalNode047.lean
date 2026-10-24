/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode046
import Proofs.RadenkovicGutmanD4Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e047 : NestedArithmetic.Expr 3 := .times e046 e028
noncomputable def p047 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,24],[24]],[[0,0],[0]],[[432,104],[104]],[[0,0],[0]],[[3024,128],[128]],[[0,0],[0]],[[8352,56],[56]],[[0,0],[0]],[[12112,8],[8]],[[0]],[[10176]],[[0]],[[5104]],[[0]],[[1504]],[[0]],[[240]],[[0]],[[16]]]
theorem step047 : p047=NestedArithmetic.mul p046 p028 := by decide +kernel
#print axioms step047
theorem h047 : NestedArithmetic.compile e047=p047 := StagedExprCompile.compile_times e047 e046 e028 p046 p028 p047 rfl h046 h028 step047
#print axioms h047
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
