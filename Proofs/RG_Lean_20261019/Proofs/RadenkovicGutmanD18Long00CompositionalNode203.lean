/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode202
import Proofs.RadenkovicGutmanD18Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[52,0],[0,0]],[[0,0],[0,0]],[[550,0],[0,0]],[[0,0],[0,0]],[[3158,0],[0,0]],[[0,0],[0,0]],[[10930,0],[0,0]],[[0,0],[0,0]],[[23736,2],[2,0]],[[0,0],[0,0]],[[32452,34],[34,0]],[[0,0],[0,0]],[[27134,188],[188,0]],[[0,0],[0,0]],[[12864,444],[444,0]],[[0,0],[0,0]],[[2880,450],[450,0]],[[0,0],[0,0]],[[162,162],[162,2]],[[0],[0,0]],[[0],[0,18]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
