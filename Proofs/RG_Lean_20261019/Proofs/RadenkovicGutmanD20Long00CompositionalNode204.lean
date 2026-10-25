/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode194
import Proofs.RadenkovicGutmanD20Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[40],[0]],[[0,0],[0]],[[640,0],[0]],[[0,0],[0]],[[4280,0],[0]],[[0,0],[0]],[[15520,0],[0]],[[0,0],[0]],[[33120,0],[0]],[[0,0],[0]],[[42240,40],[40]],[[0,0],[0]],[[31160,280],[280]],[[0,0],[0]],[[12000,640],[640]],[[0,0],[0]],[[1800,520],[520]],[[0,0],[0]],[[0,120],[120]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
