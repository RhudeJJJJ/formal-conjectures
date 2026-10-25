/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode041
import Proofs.RadenkovicGutmanD33Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,99],[99,-62]],[[0,0],[0]],[[2412,-129],[-129]],[[0,0],[0]],[[12912,-960],[-960]],[[0,0],[0]],[[26218,-1133],[-1133]],[[0,0],[0]],[[21758,-463],[-463]],[[0,0],[0]],[[-1344,-62],[-62]],[[0]],[[-16378]],[[0]],[[-12926]],[[0]],[[-4726]],[[0]],[[-856]],[[0]],[[-62]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
