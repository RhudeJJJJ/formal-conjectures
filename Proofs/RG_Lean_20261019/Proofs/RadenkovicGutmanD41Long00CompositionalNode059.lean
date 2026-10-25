/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode058
import Proofs.RadenkovicGutmanD41Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-78]],[[0,0],[0]],[[-702,-702],[-702]],[[0,0],[0]],[[-12402,-1872],[-1872]],[[0,0],[0]],[[-54366,-1716],[-1716]],[[0,0],[0]],[[-111540,-624],[-624]],[[0,0],[0]],[[-128232,-78],[-78]],[[0]],[[-88608]],[[0]],[[-37518]],[[0]],[[-9516]],[[0]],[[-1326]],[[0]],[[-78]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
