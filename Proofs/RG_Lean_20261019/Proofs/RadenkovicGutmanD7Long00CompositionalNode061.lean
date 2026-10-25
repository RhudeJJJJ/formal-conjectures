/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode059
import Proofs.RadenkovicGutmanD7Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,21],[21,-10]],[[0,0],[0]],[[225,1],[1]],[[0,0],[0]],[[510,-128],[-128]],[[0,0],[0]],[[-1517,-171],[-171]],[[0,0],[0]],[[-6908,-73],[-73]],[[0,0],[0]],[[-10644,-10],[-10]],[[0]],[[-8644]],[[0]],[[-4061]],[[0]],[[-1108]],[[0]],[[-163]],[[0]],[[-10]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
