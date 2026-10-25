/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode041
import Proofs.RadenkovicGutmanD9Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,27],[27,-14]],[[0,0],[0]],[[684,-9],[-9]],[[0,0],[0]],[[3984,-192],[-192]],[[0,0],[0]],[[9178,-245],[-245]],[[0,0],[0]],[[10094,-103],[-103]],[[0,0],[0]],[[4416,-14],[-14]],[[0]],[[-1162]],[[0]],[[-2126]],[[0]],[[-934]],[[0]],[[-184]],[[0]],[[-14]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
