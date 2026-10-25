/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode065
import Proofs.RadenkovicGutmanD30Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-30]],[[0,0],[0,0]],[[-270,-450],[-450,-2]],[[0,0],[0]],[[-7488,-1518],[-1518]],[[0,0],[0]],[[-39228,-1668],[-1668]],[[0,0],[0]],[[-91034,-704],[-704]],[[0,0],[0]],[[-115540,-106],[-106]],[[0,0],[0]],[[-87048,-2],[-2]],[[0]],[[-39982]],[[0]],[[-11042]],[[0]],[[-1714]],[[0]],[[-124]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
