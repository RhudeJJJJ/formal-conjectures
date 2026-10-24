/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode193
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e194 : NestedArithmetic.Expr 3 := .times e193 e003
noncomputable def p194 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[16,0],[0]],[[0,0],[0]],[[240,0],[0]],[[0,0],[0]],[[1504,0],[0]],[[0,0],[0]],[[5104,0],[0]],[[0,0],[0]],[[10176,0],[0]],[[0,0],[0]],[[12112,8],[8]],[[0,0],[0]],[[8352,56],[56]],[[0,0],[0]],[[3024,128],[128]],[[0,0],[0]],[[432,104],[104]],[[0,0],[0]],[[0,24],[24]]]
theorem step194 : p194=NestedArithmetic.mul p193 p003 := by decide +kernel
#print axioms step194
theorem h194 : NestedArithmetic.compile e194=p194 := StagedExprCompile.compile_times e194 e193 e003 p193 p003 p194 rfl h193 h003 step194
#print axioms h194
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
