/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode189
import Proofs.RadenkovicGutmanD4Long00CompositionalNode157
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e190 : NestedArithmetic.Expr 3 := .times e189 e157
noncomputable def p190 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[34,0],[0,0]],[[0,0],[0,0]],[[248,0],[0,0]],[[0,0],[0,0]],[[1014,0],[0,0]],[[0,0],[0,0]],[[2548,0],[0,0]],[[0,0],[0,0]],[[4056,2],[2,0]],[[0,0],[0,0]],[[4052,20],[20,0]],[[0,0],[0,0]],[[2390,76],[76,0]],[[0,0],[0,0]],[[674,136],[136,0]],[[0,0],[0,0]],[[-6,114],[114,0]],[[0,0],[0,0]],[[-36,36],[36,2]],[[0],[0,0]],[[0],[0,4]]]
theorem step190 : p190=NestedArithmetic.mul p189 p157 := by decide +kernel
#print axioms step190
theorem h190 : NestedArithmetic.compile e190=p190 := StagedExprCompile.compile_times e190 e189 e157 p189 p157 p190 rfl h189 h157 step190
#print axioms h190
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
