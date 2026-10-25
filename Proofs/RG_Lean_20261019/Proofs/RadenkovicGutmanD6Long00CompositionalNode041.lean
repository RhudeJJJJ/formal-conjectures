/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode036
import Proofs.RadenkovicGutmanD6Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-8]],[[0,0],[0]],[[144,-72],[-72]],[[0,0],[0]],[[600,-192],[-192]],[[0,0],[0]],[[784,-176],[-176]],[[0,0],[0]],[[-448,-64],[-64]],[[0,0],[0]],[[-2496,-8],[-8]],[[0]],[[-3088]],[[0]],[[-1904]],[[0]],[[-640]],[[0]],[[-112]],[[0]],[[-8]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
