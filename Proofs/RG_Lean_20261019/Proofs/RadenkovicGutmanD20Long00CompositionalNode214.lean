/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode030
import Proofs.RadenkovicGutmanD20Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[20],[0]],[[0,0],[0]],[[340,0],[0,0]],[[0,0],[0,0]],[[2440,0],[0,0]],[[0,0],[0,0]],[[9620,0],[0,0]],[[0,0],[0,0]],[[22720,0],[0,0]],[[0,0],[0,0]],[[32880,20],[20,0]],[[0,0],[0,0]],[[28600,160],[160,0]],[[0,0],[0,0]],[[13940,440],[440,0]],[[0,0],[0,0]],[[3180,480],[480,0]],[[0,0],[0,0]],[[180,180],[180,0]],[[0],[0,0]],[[0],[0,20]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
