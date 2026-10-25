/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode202
import Proofs.RadenkovicGutmanD21Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[55,0],[0,0]],[[0,0],[0,0]],[[601,0],[0,0]],[[0,0],[0,0]],[[3524,0],[0,0]],[[0,0],[0,0]],[[12373,0],[0,0]],[[0,0],[0,0]],[[27144,2],[2,0]],[[0,0],[0,0]],[[37384,37],[37,0]],[[0,0],[0,0]],[[31424,212],[212,0]],[[0,0],[0,0]],[[14955,510],[510,0]],[[0,0],[0,0]],[[3357,522],[522,0]],[[0,0],[0,0]],[[189,189],[189,2]],[[0],[0,0]],[[0],[0,21]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
