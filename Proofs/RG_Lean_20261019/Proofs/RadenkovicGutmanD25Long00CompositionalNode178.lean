/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode177
import Proofs.RadenkovicGutmanD25Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-46],[0]],[[0,0],[0]],[[-782,0],[0,0]],[[0,0],[0,0]],[[-5612,0],[0,0]],[[0,0],[0,0]],[[-22126,0],[0,0]],[[0,0],[0,0]],[[-52256,0],[0,0]],[[0,0],[0,0]],[[-75624,-46],[-46,0]],[[0,0],[0,0]],[[-65780,-368],[-368,0]],[[0,0],[0,0]],[[-32062,-1012],[-1012,0]],[[0,0],[0,0]],[[-7314,-1104],[-1104,0]],[[0,0],[0,0]],[[-414,-414],[-414,0]],[[0],[0,0]],[[0],[0,-46]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
