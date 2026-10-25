/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode041
import Proofs.RadenkovicGutmanD25Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,75],[75,-46]],[[0,0],[0]],[[1836,-89],[-89]],[[0,0],[0]],[[9936,-704],[-704]],[[0,0],[0]],[[20538,-837],[-837]],[[0,0],[0]],[[17870,-343],[-343]],[[0,0],[0]],[[576,-46],[-46]],[[0]],[[-11306]],[[0]],[[-9326]],[[0]],[[-3462]],[[0]],[[-632]],[[0]],[[-46]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
