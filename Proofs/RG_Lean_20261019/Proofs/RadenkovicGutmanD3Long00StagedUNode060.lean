/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode058
import Proofs.RadenkovicGutmanD3Long00StagedUNode059
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e060 : NestedArithmetic.Expr 3 := .plus e058 e059
noncomputable def p060 : NestedHorner.Poly 3 := [[[0],[0]],[[0,9],[9,-2]],[[0,0],[0]],[[117,21],[21]],[[0,0],[0]],[[582,0],[0]],[[0,0],[0]],[[943,-23],[-23]],[[0,0],[0]],[[308,-13],[-13]],[[0,0],[0]],[[-804,-2],[-2]],[[0]],[[-1108]],[[0]],[[-641]],[[0]],[[-196]],[[0]],[[-31]],[[0]],[[-2]]]
theorem step060 : p060=NestedHorner.add p058 p059 := by decide +kernel
#print axioms step060
theorem h060 : NestedArithmetic.compile e060=p060 := StagedExprCompile.compile_plus e060 e058 e059 p058 p059 p060 rfl h058 h059 step060
#print axioms h060
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
