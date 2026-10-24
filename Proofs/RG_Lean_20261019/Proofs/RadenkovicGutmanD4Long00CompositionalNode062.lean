/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode046
import Proofs.RadenkovicGutmanD4Long00CompositionalNode055
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e046 e055
noncomputable def p062 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,24],[24]],[[0,0],[0]],[[360,104],[104]],[[0,0],[0]],[[2400,128],[128]],[[0,0],[0]],[[6232,56],[56]],[[0,0],[0]],[[8448,8],[8]],[[0]],[[6624]],[[0]],[[3104]],[[0]],[[856]],[[0]],[[128]],[[0]],[[8]]]
theorem step062 : p062=NestedArithmetic.mul p046 p055 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e046 e055 p046 p055 p062 rfl h046 h055 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
