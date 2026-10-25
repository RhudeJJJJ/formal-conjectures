/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode041
import Proofs.RadenkovicGutmanD43Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,129],[129,-82]],[[0,0],[0]],[[3132,-179],[-179]],[[0,0],[0]],[[16632,-1280],[-1280]],[[0,0],[0]],[[33318,-1503],[-1503]],[[0,0],[0]],[[26618,-613],[-613]],[[0,0],[0]],[[-3744,-82],[-82]],[[0]],[[-22718]],[[0]],[[-17426]],[[0]],[[-6306]],[[0]],[[-1136]],[[0]],[[-82]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
