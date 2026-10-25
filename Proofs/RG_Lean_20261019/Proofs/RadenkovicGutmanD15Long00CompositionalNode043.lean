/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode041
import Proofs.RadenkovicGutmanD15Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,45],[45,-26]],[[0,0],[0]],[[1116,-39],[-39]],[[0,0],[0]],[[6216,-384],[-384]],[[0,0],[0]],[[13438,-467],[-467]],[[0,0],[0]],[[13010,-193],[-193]],[[0,0],[0]],[[2976,-26],[-26]],[[0]],[[-4966]],[[0]],[[-4826]],[[0]],[[-1882]],[[0]],[[-352]],[[0]],[[-26]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
