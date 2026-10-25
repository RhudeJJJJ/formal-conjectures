/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode194
import Proofs.RadenkovicGutmanD30Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[60],[0]],[[0,0],[0]],[[960,0],[0]],[[0,0],[0]],[[6420,0],[0]],[[0,0],[0]],[[23280,0],[0]],[[0,0],[0]],[[49680,0],[0]],[[0,0],[0]],[[63360,60],[60]],[[0,0],[0]],[[46740,420],[420]],[[0,0],[0]],[[18000,960],[960]],[[0,0],[0]],[[2700,780],[780]],[[0,0],[0]],[[0,180],[180]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
