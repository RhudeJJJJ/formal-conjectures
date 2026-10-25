/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode184
import Proofs.RadenkovicGutmanD8Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[8,0],[0]],[[0,0],[0]],[[128,0],[0]],[[0,0],[0]],[[856,0],[0]],[[0,0],[0]],[[3104,0],[0]],[[0,0],[0]],[[6624,0],[0]],[[0,0],[0]],[[8448,8],[8]],[[0,0],[0]],[[6232,56],[56]],[[0,0],[0]],[[2400,128],[128]],[[0,0],[0]],[[360,104],[104]],[[0,0],[0]],[[0,24],[24]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
