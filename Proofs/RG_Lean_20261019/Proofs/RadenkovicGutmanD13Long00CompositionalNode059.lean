/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode058
import Proofs.RadenkovicGutmanD13Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-22]],[[0,0],[0]],[[-198,-198],[-198]],[[0,0],[0]],[[-3498,-528],[-528]],[[0,0],[0]],[[-15334,-484],[-484]],[[0,0],[0]],[[-31460,-176],[-176]],[[0,0],[0]],[[-36168,-22],[-22]],[[0]],[[-24992]],[[0]],[[-10582]],[[0]],[[-2684]],[[0]],[[-374]],[[0]],[[-22]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
