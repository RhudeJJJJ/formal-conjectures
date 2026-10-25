/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode194
import Proofs.RadenkovicGutmanD41Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[82],[0]],[[0,0],[0]],[[1312,0],[0]],[[0,0],[0]],[[8774,0],[0]],[[0,0],[0]],[[31816,0],[0]],[[0,0],[0]],[[67896,0],[0]],[[0,0],[0]],[[86592,82],[82]],[[0,0],[0]],[[63878,574],[574]],[[0,0],[0]],[[24600,1312],[1312]],[[0,0],[0]],[[3690,1066],[1066]],[[0,0],[0]],[[0,246],[246]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
