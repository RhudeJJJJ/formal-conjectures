/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode065
import Proofs.RadenkovicGutmanD12Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-12]],[[0,0],[0,0]],[[-108,-180],[-180,-2]],[[0,0],[0]],[[-3006,-618],[-618]],[[0,0],[0]],[[-15882,-696],[-696]],[[0,0],[0]],[[-37250,-308],[-308]],[[0,0],[0]],[[-47932,-52],[-52]],[[0,0],[0]],[[-36792,-2],[-2]],[[0]],[[-17356]],[[0]],[[-4994]],[[0]],[[-832]],[[0]],[[-70]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
