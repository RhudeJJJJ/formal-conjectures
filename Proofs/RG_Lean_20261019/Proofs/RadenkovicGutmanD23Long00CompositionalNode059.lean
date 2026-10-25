/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode058
import Proofs.RadenkovicGutmanD23Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-42]],[[0,0],[0]],[[-378,-378],[-378]],[[0,0],[0]],[[-6678,-1008],[-1008]],[[0,0],[0]],[[-29274,-924],[-924]],[[0,0],[0]],[[-60060,-336],[-336]],[[0,0],[0]],[[-69048,-42],[-42]],[[0]],[[-47712]],[[0]],[[-20202]],[[0]],[[-5124]],[[0]],[[-714]],[[0]],[[-42]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
