/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode204
import Proofs.RadenkovicGutmanD23Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[46,0],[0]],[[0,0],[0]],[[736,0],[0]],[[0,0],[0]],[[4922,0],[0]],[[0,0],[0]],[[17848,0],[0]],[[0,0],[0]],[[38088,0],[0]],[[0,0],[0]],[[48576,46],[46]],[[0,0],[0]],[[35834,322],[322]],[[0,0],[0]],[[13800,736],[736]],[[0,0],[0]],[[2070,598],[598]],[[0,0],[0]],[[0,138],[138]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
