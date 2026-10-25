/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode058
import Proofs.RadenkovicGutmanD18Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-32]],[[0,0],[0]],[[-288,-288],[-288]],[[0,0],[0]],[[-5088,-768],[-768]],[[0,0],[0]],[[-22304,-704],[-704]],[[0,0],[0]],[[-45760,-256],[-256]],[[0,0],[0]],[[-52608,-32],[-32]],[[0]],[[-36352]],[[0]],[[-15392]],[[0]],[[-3904]],[[0]],[[-544]],[[0]],[[-32]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
