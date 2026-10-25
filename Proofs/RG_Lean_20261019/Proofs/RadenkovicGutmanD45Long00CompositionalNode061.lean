/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode059
import Proofs.RadenkovicGutmanD45Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,135],[135,-86]],[[0,0],[0]],[[1251,-189],[-189]],[[0,0],[0]],[[-174,-1344],[-1344]],[[0,0],[0]],[[-24887,-1577],[-1577]],[[0,0],[0]],[[-75460,-643],[-643]],[[0,0],[0]],[[-104124,-86],[-86]],[[0]],[[-80236]],[[0]],[[-36551]],[[0]],[[-9772]],[[0]],[[-1417]],[[0]],[[-86]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
