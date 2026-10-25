/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode041
import Proofs.RadenkovicGutmanD30Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,90],[90,-56]],[[0,0],[0]],[[2196,-114],[-114]],[[0,0],[0]],[[11796,-864],[-864]],[[0,0],[0]],[[24088,-1022],[-1022]],[[0,0],[0]],[[20300,-418],[-418]],[[0,0],[0]],[[-624,-56],[-56]],[[0]],[[-14476]],[[0]],[[-11576]],[[0]],[[-4252]],[[0]],[[-772]],[[0]],[[-56]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
