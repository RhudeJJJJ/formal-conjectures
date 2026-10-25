/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode065
import Proofs.RadenkovicGutmanD38Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-38]],[[0,0],[0,0]],[[-342,-570],[-570,-2]],[[0,0],[0]],[[-9480,-1918],[-1918]],[[0,0],[0]],[[-49604,-2100],[-2100]],[[0,0],[0]],[[-114938,-880],[-880]],[[0,0],[0]],[[-145588,-130],[-130]],[[0,0],[0]],[[-109384,-2],[-2]],[[0]],[[-50038]],[[0]],[[-13730]],[[0]],[[-2106]],[[0]],[[-148]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
