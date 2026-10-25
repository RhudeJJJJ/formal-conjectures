/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode041
import Proofs.RadenkovicGutmanD7Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,21],[21,-10]],[[0,0],[0]],[[540,1],[1]],[[0,0],[0]],[[3240,-128],[-128]],[[0,0],[0]],[[7758,-171],[-171]],[[0,0],[0]],[[9122,-73],[-73]],[[0,0],[0]],[[4896,-10],[-10]],[[0]],[[106]],[[0]],[[-1226]],[[0]],[[-618]],[[0]],[[-128]],[[0]],[[-10]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
