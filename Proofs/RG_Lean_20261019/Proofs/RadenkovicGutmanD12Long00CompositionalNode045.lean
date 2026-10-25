/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode044
import Proofs.RadenkovicGutmanD12Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,12]],[[0,0],[0,0]],[[-108,108],[108,2]],[[0,0],[0]],[[18,306],[306]],[[0,0],[0]],[[2010,312],[312]],[[0,0],[0]],[[6502,140],[140]],[[0,0],[0]],[[10100,28],[28]],[[0,0],[0]],[[9144,2],[2]],[[0]],[[5100]],[[0]],[[1766]],[[0]],[[368]],[[0]],[[42]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
