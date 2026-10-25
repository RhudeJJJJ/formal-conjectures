/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode041
import Proofs.RadenkovicGutmanD8Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,24],[24,-12]],[[0,0],[0]],[[612,-4],[-4]],[[0,0],[0]],[[3612,-160],[-160]],[[0,0],[0]],[[8468,-208],[-208]],[[0,0],[0]],[[9608,-88],[-88]],[[0,0],[0]],[[4656,-12],[-12]],[[0]],[[-528]],[[0]],[[-1676]],[[0]],[[-776]],[[0]],[[-156]],[[0]],[[-12]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
