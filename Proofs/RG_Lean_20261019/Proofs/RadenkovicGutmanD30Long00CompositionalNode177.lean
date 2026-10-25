/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode174
import Proofs.RadenkovicGutmanD30Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-56],[0]],[[0,0],[0]],[[-952,0],[0,0]],[[0,0],[0,0]],[[-6832,0],[0,0]],[[0,0],[0,0]],[[-26936,0],[0,0]],[[0,0],[0,0]],[[-63616,0],[0,0]],[[0,0],[0,0]],[[-92064,-56],[-56,0]],[[0,0],[0,0]],[[-80080,-448],[-448,0]],[[0,0],[0,0]],[[-39032,-1232],[-1232,0]],[[0,0],[0,0]],[[-8904,-1344],[-1344,0]],[[0,0],[0,0]],[[-504,-504],[-504,0]],[[0],[0,0]],[[0],[0,-56]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
