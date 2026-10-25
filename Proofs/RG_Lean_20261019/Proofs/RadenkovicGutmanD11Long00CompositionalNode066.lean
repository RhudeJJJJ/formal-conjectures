/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode065
import Proofs.RadenkovicGutmanD11Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-11]],[[0,0],[0,0]],[[-99,-165],[-165,-2]],[[0,0],[0]],[[-2757,-568],[-568]],[[0,0],[0]],[[-14585,-642],[-642]],[[0,0],[0]],[[-34262,-286],[-286]],[[0,0],[0]],[[-44176,-49],[-49]],[[0,0],[0]],[[-34000,-2],[-2]],[[0]],[[-16099]],[[0]],[[-4658]],[[0]],[[-783]],[[0]],[[-67]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
