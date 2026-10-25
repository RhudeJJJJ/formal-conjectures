/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode041
import Proofs.RadenkovicGutmanD44Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,132],[132,-84]],[[0,0],[0]],[[3204,-184],[-184]],[[0,0],[0]],[[17004,-1312],[-1312]],[[0,0],[0]],[[34028,-1540],[-1540]],[[0,0],[0]],[[27104,-628],[-628]],[[0,0],[0]],[[-3984,-84],[-84]],[[0]],[[-23352]],[[0]],[[-17876]],[[0]],[[-6464]],[[0]],[[-1164]],[[0]],[[-84]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
