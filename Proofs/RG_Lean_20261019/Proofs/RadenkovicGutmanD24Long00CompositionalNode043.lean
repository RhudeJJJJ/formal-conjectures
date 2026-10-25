/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode041
import Proofs.RadenkovicGutmanD24Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,72],[72,-44]],[[0,0],[0]],[[1764,-84],[-84]],[[0,0],[0]],[[9564,-672],[-672]],[[0,0],[0]],[[19828,-800],[-800]],[[0,0],[0]],[[17384,-328],[-328]],[[0,0],[0]],[[816,-44],[-44]],[[0]],[[-10672]],[[0]],[[-8876]],[[0]],[[-3304]],[[0]],[[-604]],[[0]],[[-44]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
