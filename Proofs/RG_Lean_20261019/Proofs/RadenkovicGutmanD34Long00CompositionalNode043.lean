/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode041
import Proofs.RadenkovicGutmanD34Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,102],[102,-64]],[[0,0],[0]],[[2484,-134],[-134]],[[0,0],[0]],[[13284,-992],[-992]],[[0,0],[0]],[[26928,-1170],[-1170]],[[0,0],[0]],[[22244,-478],[-478]],[[0,0],[0]],[[-1584,-64],[-64]],[[0]],[[-17012]],[[0]],[[-13376]],[[0]],[[-4884]],[[0]],[[-884]],[[0]],[[-64]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
