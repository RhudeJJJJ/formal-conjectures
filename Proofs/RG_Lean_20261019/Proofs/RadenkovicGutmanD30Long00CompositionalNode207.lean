/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode065
import Proofs.RadenkovicGutmanD30Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-124,0],[0,0]],[[0,0],[0,0]],[[-1714,0],[0,0]],[[0,0],[0,0]],[[-11042,0],[0,0]],[[0,0],[0,0]],[[-39982,0],[0,0]],[[0,0],[0,0]],[[-87048,-2],[-2,0]],[[0,0],[0,0]],[[-115540,-106],[-106,0]],[[0,0],[0,0]],[[-91034,-704],[-704,0]],[[0,0],[0,0]],[[-39228,-1668],[-1668,0]],[[0,0],[0,0]],[[-7488,-1518],[-1518,0]],[[0,0],[0,0]],[[-270,-450],[-450,-2]],[[0],[0,0]],[[0],[0,-30]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
