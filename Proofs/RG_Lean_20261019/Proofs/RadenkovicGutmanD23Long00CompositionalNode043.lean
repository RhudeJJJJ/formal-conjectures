/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode041
import Proofs.RadenkovicGutmanD23Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,69],[69,-42]],[[0,0],[0]],[[1692,-79],[-79]],[[0,0],[0]],[[9192,-640],[-640]],[[0,0],[0]],[[19118,-763],[-763]],[[0,0],[0]],[[16898,-313],[-313]],[[0,0],[0]],[[1056,-42],[-42]],[[0]],[[-10038]],[[0]],[[-8426]],[[0]],[[-3146]],[[0]],[[-576]],[[0]],[[-42]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
