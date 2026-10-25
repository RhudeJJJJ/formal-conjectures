/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode030
import Proofs.RadenkovicGutmanD14Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[14],[0]],[[0,0],[0]],[[238,0],[0,0]],[[0,0],[0,0]],[[1708,0],[0,0]],[[0,0],[0,0]],[[6734,0],[0,0]],[[0,0],[0,0]],[[15904,0],[0,0]],[[0,0],[0,0]],[[23016,14],[14,0]],[[0,0],[0,0]],[[20020,112],[112,0]],[[0,0],[0,0]],[[9758,308],[308,0]],[[0,0],[0,0]],[[2226,336],[336,0]],[[0,0],[0,0]],[[126,126],[126,0]],[[0],[0,0]],[[0],[0,14]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
