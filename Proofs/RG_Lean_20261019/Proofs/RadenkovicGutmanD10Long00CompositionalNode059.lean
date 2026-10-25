/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode058
import Proofs.RadenkovicGutmanD10Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-16]],[[0,0],[0]],[[-144,-144],[-144]],[[0,0],[0]],[[-2544,-384],[-384]],[[0,0],[0]],[[-11152,-352],[-352]],[[0,0],[0]],[[-22880,-128],[-128]],[[0,0],[0]],[[-26304,-16],[-16]],[[0]],[[-18176]],[[0]],[[-7696]],[[0]],[[-1952]],[[0]],[[-272]],[[0]],[[-16]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
