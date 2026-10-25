/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode058
import Proofs.RadenkovicGutmanD44Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-84]],[[0,0],[0]],[[-756,-756],[-756]],[[0,0],[0]],[[-13356,-2016],[-2016]],[[0,0],[0]],[[-58548,-1848],[-1848]],[[0,0],[0]],[[-120120,-672],[-672]],[[0,0],[0]],[[-138096,-84],[-84]],[[0]],[[-95424]],[[0]],[[-40404]],[[0]],[[-10248]],[[0]],[[-1428]],[[0]],[[-84]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
