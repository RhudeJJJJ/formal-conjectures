/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode192
import Proofs.RadenkovicGutmanD18Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[48,0],[0,0]],[[0,0],[0,0]],[[458,0],[0,0]],[[0,0],[0,0]],[[2330,0],[0,0]],[[0,0],[0,0]],[[7014,0],[0,0]],[[0,0],[0,0]],[[12960,2],[2,0]],[[0,0],[0,0]],[[14636,34],[34,0]],[[0,0],[0,0]],[[9586,188],[188,0]],[[0,0],[0,0]],[[3012,444],[444,0]],[[0,0],[0,0]],[[36,450],[450,0]],[[0,0],[0,0]],[[-162,162],[162,2]],[[0],[0,0]],[[0],[0,18]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
