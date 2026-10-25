/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode177
import Proofs.RadenkovicGutmanD32Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-60],[0]],[[0,0],[0]],[[-1020,0],[0,0]],[[0,0],[0,0]],[[-7320,0],[0,0]],[[0,0],[0,0]],[[-28860,0],[0,0]],[[0,0],[0,0]],[[-68160,0],[0,0]],[[0,0],[0,0]],[[-98640,-60],[-60,0]],[[0,0],[0,0]],[[-85800,-480],[-480,0]],[[0,0],[0,0]],[[-41820,-1320],[-1320,0]],[[0,0],[0,0]],[[-9540,-1440],[-1440,0]],[[0,0],[0,0]],[[-540,-540],[-540,0]],[[0],[0,0]],[[0],[0,-60]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
