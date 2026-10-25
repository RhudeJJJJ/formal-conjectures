/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode065
import Proofs.RadenkovicGutmanD45Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-45]],[[0,0],[0,0]],[[-405,-675],[-675,-2]],[[0,0],[0]],[[-11223,-2268],[-2268]],[[0,0],[0]],[[-58683,-2478],[-2478]],[[0,0],[0]],[[-135854,-1034],[-1034]],[[0,0],[0]],[[-171880,-151],[-151]],[[0,0],[0]],[[-128928,-2],[-2]],[[0]],[[-58837]],[[0]],[[-16082]],[[0]],[[-2449]],[[0]],[[-169]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
