/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode041
import Proofs.RadenkovicGutmanD6Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,18],[18,-8]],[[0,0],[0]],[[468,6],[6]],[[0,0],[0]],[[2868,-96],[-96]],[[0,0],[0]],[[7048,-134],[-134]],[[0,0],[0]],[[8636,-58],[-58]],[[0,0],[0]],[[5136,-8],[-8]],[[0]],[[740]],[[0]],[[-776]],[[0]],[[-460]],[[0]],[[-100]],[[0]],[[-8]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
