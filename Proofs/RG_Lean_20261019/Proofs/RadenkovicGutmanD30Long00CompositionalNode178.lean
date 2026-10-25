/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode177
import Proofs.RadenkovicGutmanD30Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-56],[0]],[[0,0],[0]],[[-952,0],[0,0]],[[0,0],[0,0]],[[-6832,0],[0,0]],[[0,0],[0,0]],[[-26936,0],[0,0]],[[0,0],[0,0]],[[-63616,0],[0,0]],[[0,0],[0,0]],[[-92064,-56],[-56,0]],[[0,0],[0,0]],[[-80080,-448],[-448,0]],[[0,0],[0,0]],[[-39032,-1232],[-1232,0]],[[0,0],[0,0]],[[-8904,-1344],[-1344,0]],[[0,0],[0,0]],[[-504,-504],[-504,0]],[[0],[0,0]],[[0],[0,-56]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
