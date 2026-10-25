/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode044
import Proofs.RadenkovicGutmanD42Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,42]],[[0,0],[0,0]],[[-378,378],[378,2]],[[0,0],[0]],[[108,1026],[1026]],[[0,0],[0]],[[7020,972],[972]],[[0,0],[0]],[[21922,380],[380]],[[0,0],[0]],[[32780,58],[58]],[[0,0],[0]],[[28224,2],[2]],[[0]],[[14670]],[[0]],[[4586]],[[0]],[[818]],[[0]],[[72]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
