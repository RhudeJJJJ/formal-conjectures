/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode191
import Proofs.RadenkovicGutmanD21Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[55,0],[0,0]],[[0,0],[0,0]],[[601,0],[0,0]],[[0,0],[0,0]],[[3524,0],[0,0]],[[0,0],[0,0]],[[12373,0],[0,0]],[[0,0],[0,0]],[[27144,2],[2,0]],[[0,0],[0,0]],[[37384,37],[37,0]],[[0,0],[0,0]],[[31424,212],[212,0]],[[0,0],[0,0]],[[14955,510],[510,0]],[[0,0],[0,0]],[[3357,522],[522,0]],[[0,0],[0,0]],[[189,189],[189,2]],[[0],[0,0]],[[0],[0,21]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
