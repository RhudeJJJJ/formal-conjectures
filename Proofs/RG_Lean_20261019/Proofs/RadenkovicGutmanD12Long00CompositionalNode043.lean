/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode041
import Proofs.RadenkovicGutmanD12Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,36],[36,-20]],[[0,0],[0]],[[900,-24],[-24]],[[0,0],[0]],[[5100,-288],[-288]],[[0,0],[0]],[[11308,-356],[-356]],[[0,0],[0]],[[11552,-148],[-148]],[[0,0],[0]],[[3696,-20],[-20]],[[0]],[[-3064]],[[0]],[[-3476]],[[0]],[[-1408]],[[0]],[[-268]],[[0]],[[-20]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
