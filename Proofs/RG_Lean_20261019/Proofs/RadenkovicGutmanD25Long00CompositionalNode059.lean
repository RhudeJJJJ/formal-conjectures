/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode058
import Proofs.RadenkovicGutmanD25Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-46]],[[0,0],[0]],[[-414,-414],[-414]],[[0,0],[0]],[[-7314,-1104],[-1104]],[[0,0],[0]],[[-32062,-1012],[-1012]],[[0,0],[0]],[[-65780,-368],[-368]],[[0,0],[0]],[[-75624,-46],[-46]],[[0]],[[-52256]],[[0]],[[-22126]],[[0]],[[-5612]],[[0]],[[-782]],[[0]],[[-46]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
