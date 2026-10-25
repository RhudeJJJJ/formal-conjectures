/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode177
import Proofs.RadenkovicGutmanD27Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-50],[0]],[[0,0],[0]],[[-850,0],[0,0]],[[0,0],[0,0]],[[-6100,0],[0,0]],[[0,0],[0,0]],[[-24050,0],[0,0]],[[0,0],[0,0]],[[-56800,0],[0,0]],[[0,0],[0,0]],[[-82200,-50],[-50,0]],[[0,0],[0,0]],[[-71500,-400],[-400,0]],[[0,0],[0,0]],[[-34850,-1100],[-1100,0]],[[0,0],[0,0]],[[-7950,-1200],[-1200,0]],[[0,0],[0,0]],[[-450,-450],[-450,0]],[[0],[0,0]],[[0],[0,-50]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
