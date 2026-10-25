/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode041
import Proofs.RadenkovicGutmanD32Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,96],[96,-60]],[[0,0],[0]],[[2340,-124],[-124]],[[0,0],[0]],[[12540,-928],[-928]],[[0,0],[0]],[[25508,-1096],[-1096]],[[0,0],[0]],[[21272,-448],[-448]],[[0,0],[0]],[[-1104,-60],[-60]],[[0]],[[-15744]],[[0]],[[-12476]],[[0]],[[-4568]],[[0]],[[-828]],[[0]],[[-60]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
