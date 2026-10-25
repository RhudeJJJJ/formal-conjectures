/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode044
import Proofs.RadenkovicGutmanD21Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,21]],[[0,0],[0,0]],[[189,189],[189,2]],[[0,0],[0]],[[3357,522],[522]],[[0,0],[0]],[[14955,510],[510]],[[0,0],[0]],[[31424,212],[212]],[[0,0],[0]],[[37384,37],[37]],[[0,0],[0]],[[27144,2],[2]],[[0]],[[12373]],[[0]],[[3524]],[[0]],[[601]],[[0]],[[55]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
