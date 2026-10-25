/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode030
import Proofs.RadenkovicGutmanD44Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[44],[0]],[[0,0],[0]],[[660,0],[0,0]],[[0,0],[0,0]],[[4136,0],[0,0]],[[0,0],[0,0]],[[14036,0],[0,0]],[[0,0],[0,0]],[[27984,0],[0,0]],[[0,0],[0,0]],[[33264,44],[44,0]],[[0,0],[0,0]],[[22616,352],[352,0]],[[0,0],[0,0]],[[7348,968],[968,0]],[[0,0],[0,0]],[[132,1056],[1056,0]],[[0,0],[0,0]],[[-396,396],[396,0]],[[0],[0,0]],[[0],[0,44]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
