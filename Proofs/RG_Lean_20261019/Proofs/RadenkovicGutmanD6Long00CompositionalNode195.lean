/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode194
import Proofs.RadenkovicGutmanD6Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[24],[0]],[[0,0],[0]],[[360,0],[0]],[[0,0],[0]],[[2256,0],[0]],[[0,0],[0]],[[7656,0],[0]],[[0,0],[0]],[[15264,0],[0]],[[0,0],[0]],[[18168,12],[12]],[[0,0],[0]],[[12528,84],[84]],[[0,0],[0]],[[4536,192],[192]],[[0,0],[0]],[[648,156],[156]],[[0,0],[0]],[[0,36],[36]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
