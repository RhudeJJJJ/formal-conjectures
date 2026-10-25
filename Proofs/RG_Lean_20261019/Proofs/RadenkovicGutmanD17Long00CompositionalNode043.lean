/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode041
import Proofs.RadenkovicGutmanD17Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,51],[51,-30]],[[0,0],[0]],[[1260,-49],[-49]],[[0,0],[0]],[[6960,-448],[-448]],[[0,0],[0]],[[14858,-541],[-541]],[[0,0],[0]],[[13982,-223],[-223]],[[0,0],[0]],[[2496,-30],[-30]],[[0]],[[-6234]],[[0]],[[-5726]],[[0]],[[-2198]],[[0]],[[-408]],[[0]],[[-30]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
