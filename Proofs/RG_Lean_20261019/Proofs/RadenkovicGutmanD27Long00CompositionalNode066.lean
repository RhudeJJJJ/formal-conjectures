/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode065
import Proofs.RadenkovicGutmanD27Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-27]],[[0,0],[0,0]],[[-243,-405],[-405,-2]],[[0,0],[0]],[[-6741,-1368],[-1368]],[[0,0],[0]],[[-35337,-1506],[-1506]],[[0,0],[0]],[[-82070,-638],[-638]],[[0,0],[0]],[[-104272,-97],[-97]],[[0,0],[0]],[[-78672,-2],[-2]],[[0]],[[-36211]],[[0]],[[-10034]],[[0]],[[-1567]],[[0]],[[-115]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
