/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode041
import Proofs.RadenkovicGutmanD22Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,66],[66,-40]],[[0,0],[0]],[[1620,-74],[-74]],[[0,0],[0]],[[8820,-608],[-608]],[[0,0],[0]],[[18408,-726],[-726]],[[0,0],[0]],[[16412,-298],[-298]],[[0,0],[0]],[[1296,-40],[-40]],[[0]],[[-9404]],[[0]],[[-7976]],[[0]],[[-2988]],[[0]],[[-548]],[[0]],[[-40]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
