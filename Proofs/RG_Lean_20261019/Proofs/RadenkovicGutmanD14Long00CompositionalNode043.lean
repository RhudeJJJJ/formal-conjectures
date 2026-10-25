/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode041
import Proofs.RadenkovicGutmanD14Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,42],[42,-24]],[[0,0],[0]],[[1044,-34],[-34]],[[0,0],[0]],[[5844,-352],[-352]],[[0,0],[0]],[[12728,-430],[-430]],[[0,0],[0]],[[12524,-178],[-178]],[[0,0],[0]],[[3216,-24],[-24]],[[0]],[[-4332]],[[0]],[[-4376]],[[0]],[[-1724]],[[0]],[[-324]],[[0]],[[-24]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
