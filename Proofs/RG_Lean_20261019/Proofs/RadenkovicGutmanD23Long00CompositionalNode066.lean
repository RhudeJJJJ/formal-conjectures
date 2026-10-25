/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode065
import Proofs.RadenkovicGutmanD23Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-23]],[[0,0],[0,0]],[[-207,-345],[-345,-2]],[[0,0],[0]],[[-5745,-1168],[-1168]],[[0,0],[0]],[[-30149,-1290],[-1290]],[[0,0],[0]],[[-70118,-550],[-550]],[[0,0],[0]],[[-89248,-85],[-85]],[[0,0],[0]],[[-67504,-2],[-2]],[[0]],[[-31183]],[[0]],[[-8690]],[[0]],[[-1371]],[[0]],[[-103]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
