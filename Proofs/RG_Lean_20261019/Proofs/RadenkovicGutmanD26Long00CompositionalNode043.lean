/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode041
import Proofs.RadenkovicGutmanD26Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,78],[78,-48]],[[0,0],[0]],[[1908,-94],[-94]],[[0,0],[0]],[[10308,-736],[-736]],[[0,0],[0]],[[21248,-874],[-874]],[[0,0],[0]],[[18356,-358],[-358]],[[0,0],[0]],[[336,-48],[-48]],[[0]],[[-11940]],[[0]],[[-9776]],[[0]],[[-3620]],[[0]],[[-660]],[[0]],[[-48]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
