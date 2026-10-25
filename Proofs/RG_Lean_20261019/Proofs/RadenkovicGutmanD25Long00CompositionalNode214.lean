/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode030
import Proofs.RadenkovicGutmanD25Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[25],[0]],[[0,0],[0]],[[425,0],[0,0]],[[0,0],[0,0]],[[3050,0],[0,0]],[[0,0],[0,0]],[[12025,0],[0,0]],[[0,0],[0,0]],[[28400,0],[0,0]],[[0,0],[0,0]],[[41100,25],[25,0]],[[0,0],[0,0]],[[35750,200],[200,0]],[[0,0],[0,0]],[[17425,550],[550,0]],[[0,0],[0,0]],[[3975,600],[600,0]],[[0,0],[0,0]],[[225,225],[225,0]],[[0],[0,0]],[[0],[0,25]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
