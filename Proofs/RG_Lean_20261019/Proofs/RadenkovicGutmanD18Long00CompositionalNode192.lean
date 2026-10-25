/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode191
import Proofs.RadenkovicGutmanD18Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[48,0],[0,0]],[[0,0],[0,0]],[[458,0],[0,0]],[[0,0],[0,0]],[[2330,0],[0,0]],[[0,0],[0,0]],[[7014,0],[0,0]],[[0,0],[0,0]],[[12960,2],[2,0]],[[0,0],[0,0]],[[14636,34],[34,0]],[[0,0],[0,0]],[[9586,188],[188,0]],[[0,0],[0,0]],[[3012,444],[444,0]],[[0,0],[0,0]],[[36,450],[450,0]],[[0,0],[0,0]],[[-162,162],[162,2]],[[0],[0,0]],[[0],[0,18]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
