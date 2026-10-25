/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode041
import Proofs.RadenkovicGutmanD18Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,54],[54,-32]],[[0,0],[0]],[[1332,-54],[-54]],[[0,0],[0]],[[7332,-480],[-480]],[[0,0],[0]],[[15568,-578],[-578]],[[0,0],[0]],[[14468,-238],[-238]],[[0,0],[0]],[[2256,-32],[-32]],[[0]],[[-6868]],[[0]],[[-6176]],[[0]],[[-2356]],[[0]],[[-436]],[[0]],[[-32]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
