/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode058
import Proofs.RadenkovicGutmanD33Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-62]],[[0,0],[0]],[[-558,-558],[-558]],[[0,0],[0]],[[-9858,-1488],[-1488]],[[0,0],[0]],[[-43214,-1364],[-1364]],[[0,0],[0]],[[-88660,-496],[-496]],[[0,0],[0]],[[-101928,-62],[-62]],[[0]],[[-70432]],[[0]],[[-29822]],[[0]],[[-7564]],[[0]],[[-1054]],[[0]],[[-62]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
