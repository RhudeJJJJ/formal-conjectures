/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode030
import Proofs.RadenkovicGutmanD22Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[22],[0]],[[0,0],[0]],[[374,0],[0,0]],[[0,0],[0,0]],[[2684,0],[0,0]],[[0,0],[0,0]],[[10582,0],[0,0]],[[0,0],[0,0]],[[24992,0],[0,0]],[[0,0],[0,0]],[[36168,22],[22,0]],[[0,0],[0,0]],[[31460,176],[176,0]],[[0,0],[0,0]],[[15334,484],[484,0]],[[0,0],[0,0]],[[3498,528],[528,0]],[[0,0],[0,0]],[[198,198],[198,0]],[[0],[0,0]],[[0],[0,22]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
