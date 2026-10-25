/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode030
import Proofs.RadenkovicGutmanD32Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[32],[0]],[[0,0],[0]],[[544,0],[0,0]],[[0,0],[0,0]],[[3904,0],[0,0]],[[0,0],[0,0]],[[15392,0],[0,0]],[[0,0],[0,0]],[[36352,0],[0,0]],[[0,0],[0,0]],[[52608,32],[32,0]],[[0,0],[0,0]],[[45760,256],[256,0]],[[0,0],[0,0]],[[22304,704],[704,0]],[[0,0],[0,0]],[[5088,768],[768,0]],[[0,0],[0,0]],[[288,288],[288,0]],[[0],[0,0]],[[0],[0,32]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
