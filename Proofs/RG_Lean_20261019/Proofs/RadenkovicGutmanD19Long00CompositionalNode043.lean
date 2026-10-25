/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode041
import Proofs.RadenkovicGutmanD19Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,57],[57,-34]],[[0,0],[0]],[[1404,-59],[-59]],[[0,0],[0]],[[7704,-512],[-512]],[[0,0],[0]],[[16278,-615],[-615]],[[0,0],[0]],[[14954,-253],[-253]],[[0,0],[0]],[[2016,-34],[-34]],[[0]],[[-7502]],[[0]],[[-6626]],[[0]],[[-2514]],[[0]],[[-464]],[[0]],[[-34]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
