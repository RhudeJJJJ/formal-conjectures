/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode174
import Proofs.RadenkovicGutmanD32Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-60],[0]],[[0,0],[0]],[[-1020,0],[0,0]],[[0,0],[0,0]],[[-7320,0],[0,0]],[[0,0],[0,0]],[[-28860,0],[0,0]],[[0,0],[0,0]],[[-68160,0],[0,0]],[[0,0],[0,0]],[[-98640,-60],[-60,0]],[[0,0],[0,0]],[[-85800,-480],[-480,0]],[[0,0],[0,0]],[[-41820,-1320],[-1320,0]],[[0,0],[0,0]],[[-9540,-1440],[-1440,0]],[[0,0],[0,0]],[[-540,-540],[-540,0]],[[0],[0,0]],[[0],[0,-60]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
