/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode030
import Proofs.RadenkovicGutmanD15Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[15],[0]],[[0,0],[0]],[[225,0],[0,0]],[[0,0],[0,0]],[[1410,0],[0,0]],[[0,0],[0,0]],[[4785,0],[0,0]],[[0,0],[0,0]],[[9540,0],[0,0]],[[0,0],[0,0]],[[11340,15],[15,0]],[[0,0],[0,0]],[[7710,120],[120,0]],[[0,0],[0,0]],[[2505,330],[330,0]],[[0,0],[0,0]],[[45,360],[360,0]],[[0,0],[0,0]],[[-135,135],[135,0]],[[0],[0,0]],[[0],[0,15]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
