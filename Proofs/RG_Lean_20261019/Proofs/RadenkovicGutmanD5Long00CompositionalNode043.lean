/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode041
import Proofs.RadenkovicGutmanD5Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,15],[15,-6]],[[0,0],[0]],[[396,11],[11]],[[0,0],[0]],[[2496,-64],[-64]],[[0,0],[0]],[[6338,-97],[-97]],[[0,0],[0]],[[8150,-43],[-43]],[[0,0],[0]],[[5376,-6],[-6]],[[0]],[[1374]],[[0]],[[-326]],[[0]],[[-302]],[[0]],[[-72]],[[0]],[[-6]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
