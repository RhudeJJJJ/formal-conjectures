/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode059
import Proofs.RadenkovicGutmanD22Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,66],[66,-40]],[[0,0],[0]],[[630,-74],[-74]],[[0,0],[0]],[[240,-608],[-608]],[[0,0],[0]],[[-10742,-726],[-726]],[[0,0],[0]],[[-33968,-298],[-298]],[[0,0],[0]],[[-47544,-40],[-40]],[[0]],[[-36904]],[[0]],[[-16886]],[[0]],[[-4528]],[[0]],[[-658]],[[0]],[[-40]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
