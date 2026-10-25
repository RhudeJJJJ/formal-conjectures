/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode041
import Proofs.RadenkovicGutmanD16Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,48],[48,-28]],[[0,0],[0]],[[1188,-44],[-44]],[[0,0],[0]],[[6588,-416],[-416]],[[0,0],[0]],[[14148,-504],[-504]],[[0,0],[0]],[[13496,-208],[-208]],[[0,0],[0]],[[2736,-28],[-28]],[[0]],[[-5600]],[[0]],[[-5276]],[[0]],[[-2040]],[[0]],[[-380]],[[0]],[[-28]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
