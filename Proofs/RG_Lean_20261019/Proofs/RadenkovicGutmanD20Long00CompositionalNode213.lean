/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode030
import Proofs.RadenkovicGutmanD20Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[20],[0]],[[0,0],[0]],[[300,0],[0,0]],[[0,0],[0,0]],[[1880,0],[0,0]],[[0,0],[0,0]],[[6380,0],[0,0]],[[0,0],[0,0]],[[12720,0],[0,0]],[[0,0],[0,0]],[[15120,20],[20,0]],[[0,0],[0,0]],[[10280,160],[160,0]],[[0,0],[0,0]],[[3340,440],[440,0]],[[0,0],[0,0]],[[60,480],[480,0]],[[0,0],[0,0]],[[-180,180],[180,0]],[[0],[0,0]],[[0],[0,20]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
