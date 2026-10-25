/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode065
import Proofs.RadenkovicGutmanD45Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-169,0],[0,0]],[[0,0],[0,0]],[[-2449,0],[0,0]],[[0,0],[0,0]],[[-16082,0],[0,0]],[[0,0],[0,0]],[[-58837,0],[0,0]],[[0,0],[0,0]],[[-128928,-2],[-2,0]],[[0,0],[0,0]],[[-171880,-151],[-151,0]],[[0,0],[0,0]],[[-135854,-1034],[-1034,0]],[[0,0],[0,0]],[[-58683,-2478],[-2478,0]],[[0,0],[0,0]],[[-11223,-2268],[-2268,0]],[[0,0],[0,0]],[[-405,-675],[-675,-2]],[[0],[0,0]],[[0],[0,-45]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
