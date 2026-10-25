/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode041
import Proofs.RadenkovicGutmanD27Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,81],[81,-50]],[[0,0],[0]],[[1980,-99],[-99]],[[0,0],[0]],[[10680,-768],[-768]],[[0,0],[0]],[[21958,-911],[-911]],[[0,0],[0]],[[18842,-373],[-373]],[[0,0],[0]],[[96,-50],[-50]],[[0]],[[-12574]],[[0]],[[-10226]],[[0]],[[-3778]],[[0]],[[-688]],[[0]],[[-50]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
