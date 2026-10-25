/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode044
import Proofs.RadenkovicGutmanD18Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,18]],[[0,0],[0,0]],[[162,162],[162,2]],[[0,0],[0]],[[2880,450],[450]],[[0,0],[0]],[[12864,444],[444]],[[0,0],[0]],[[27134,188],[188]],[[0,0],[0]],[[32452,34],[34]],[[0,0],[0]],[[23736,2],[2]],[[0]],[[10930]],[[0]],[[3158]],[[0]],[[550]],[[0]],[[52]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
