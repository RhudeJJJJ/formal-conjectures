/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode202
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e003
noncomputable def p203 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[8,0],[0]],[[0,0],[0]],[[128,0],[0]],[[0,0],[0]],[[856,0],[0]],[[0,0],[0]],[[3104,0],[0]],[[0,0],[0]],[[6624,0],[0]],[[0,0],[0]],[[8448,8],[8]],[[0,0],[0]],[[6232,56],[56]],[[0,0],[0]],[[2400,128],[128]],[[0,0],[0]],[[360,104],[104]],[[0,0],[0]],[[0,24],[24]]]
theorem step203 : p203=NestedArithmetic.mul p202 p003 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e003 p202 p003 p203 rfl h202 h003 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
