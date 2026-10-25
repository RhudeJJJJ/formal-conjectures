/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode194
import Proofs.RadenkovicGutmanD37Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[74],[0]],[[0,0],[0]],[[1184,0],[0]],[[0,0],[0]],[[7918,0],[0]],[[0,0],[0]],[[28712,0],[0]],[[0,0],[0]],[[61272,0],[0]],[[0,0],[0]],[[78144,74],[74]],[[0,0],[0]],[[57646,518],[518]],[[0,0],[0]],[[22200,1184],[1184]],[[0,0],[0]],[[3330,962],[962]],[[0,0],[0]],[[0,222],[222]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
