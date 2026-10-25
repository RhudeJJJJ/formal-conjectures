/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode059
import Proofs.RadenkovicGutmanD13Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,39],[39,-22]],[[0,0],[0]],[[387,-29],[-29]],[[0,0],[0]],[[402,-320],[-320]],[[0,0],[0]],[[-5207,-393],[-393]],[[0,0],[0]],[[-17732,-163],[-163]],[[0,0],[0]],[[-25404,-22],[-22]],[[0]],[[-19948]],[[0]],[[-9191]],[[0]],[[-2476]],[[0]],[[-361]],[[0]],[[-22]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
