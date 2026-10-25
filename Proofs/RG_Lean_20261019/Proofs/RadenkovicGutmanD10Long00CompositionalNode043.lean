/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode041
import Proofs.RadenkovicGutmanD10Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,30],[30,-16]],[[0,0],[0]],[[756,-14],[-14]],[[0,0],[0]],[[4356,-224],[-224]],[[0,0],[0]],[[9888,-282],[-282]],[[0,0],[0]],[[10580,-118],[-118]],[[0,0],[0]],[[4176,-16],[-16]],[[0]],[[-1796]],[[0]],[[-2576]],[[0]],[[-1092]],[[0]],[[-212]],[[0]],[[-16]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
