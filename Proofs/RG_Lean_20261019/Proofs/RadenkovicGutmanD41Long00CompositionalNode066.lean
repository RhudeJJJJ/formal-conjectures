/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode065
import Proofs.RadenkovicGutmanD41Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-41]],[[0,0],[0,0]],[[-369,-615],[-615,-2]],[[0,0],[0]],[[-10227,-2068],[-2068]],[[0,0],[0]],[[-53495,-2262],[-2262]],[[0,0],[0]],[[-123902,-946],[-946]],[[0,0],[0]],[[-156856,-139],[-139]],[[0,0],[0]],[[-117760,-2],[-2]],[[0]],[[-53809]],[[0]],[[-14738]],[[0]],[[-2253]],[[0]],[[-157]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
