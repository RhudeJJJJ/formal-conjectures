/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode065
import Proofs.RadenkovicGutmanD24Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-24]],[[0,0],[0,0]],[[-216,-360],[-360,-2]],[[0,0],[0]],[[-5994,-1218],[-1218]],[[0,0],[0]],[[-31446,-1344],[-1344]],[[0,0],[0]],[[-73106,-572],[-572]],[[0,0],[0]],[[-93004,-88],[-88]],[[0,0],[0]],[[-70296,-2],[-2]],[[0]],[[-32440]],[[0]],[[-9026]],[[0]],[[-1420]],[[0]],[[-106]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
