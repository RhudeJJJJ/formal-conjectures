/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode065
import Proofs.RadenkovicGutmanD6Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-52,0],[0,0]],[[0,0],[0,0]],[[-538,0],[0,0]],[[0,0],[0,0]],[[-2978,0],[0,0]],[[0,0],[0,0]],[[-9814,0],[0,0]],[[0,0],[0,0]],[[-20040,-2],[-2,0]],[[0,0],[0,0]],[[-25396,-34],[-34,0]],[[0,0],[0,0]],[[-19322,-176],[-176,0]],[[0,0],[0,0]],[[-8100,-372],[-372,0]],[[0,0],[0,0]],[[-1512,-318],[-318,0]],[[0,0],[0,0]],[[-54,-90],[-90,-2]],[[0],[0,0]],[[0],[0,-6]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
