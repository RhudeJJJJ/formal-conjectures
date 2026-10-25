/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode065
import Proofs.RadenkovicGutmanD41Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-157,0],[0,0]],[[0,0],[0,0]],[[-2253,0],[0,0]],[[0,0],[0,0]],[[-14738,0],[0,0]],[[0,0],[0,0]],[[-53809,0],[0,0]],[[0,0],[0,0]],[[-117760,-2],[-2,0]],[[0,0],[0,0]],[[-156856,-139],[-139,0]],[[0,0],[0,0]],[[-123902,-946],[-946,0]],[[0,0],[0,0]],[[-53495,-2262],[-2262,0]],[[0,0],[0,0]],[[-10227,-2068],[-2068,0]],[[0,0],[0,0]],[[-369,-615],[-615,-2]],[[0],[0,0]],[[0],[0,-41]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
