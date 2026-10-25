/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode041
import Proofs.RadenkovicGutmanD35Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,105],[105,-66]],[[0,0],[0]],[[2556,-139],[-139]],[[0,0],[0]],[[13656,-1024],[-1024]],[[0,0],[0]],[[27638,-1207],[-1207]],[[0,0],[0]],[[22730,-493],[-493]],[[0,0],[0]],[[-1824,-66],[-66]],[[0]],[[-17646]],[[0]],[[-13826]],[[0]],[[-5042]],[[0]],[[-912]],[[0]],[[-66]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
