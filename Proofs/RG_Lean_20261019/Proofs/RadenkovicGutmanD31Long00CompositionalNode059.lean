/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode058
import Proofs.RadenkovicGutmanD31Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-58]],[[0,0],[0]],[[-522,-522],[-522]],[[0,0],[0]],[[-9222,-1392],[-1392]],[[0,0],[0]],[[-40426,-1276],[-1276]],[[0,0],[0]],[[-82940,-464],[-464]],[[0,0],[0]],[[-95352,-58],[-58]],[[0]],[[-65888]],[[0]],[[-27898]],[[0]],[[-7076]],[[0]],[[-986]],[[0]],[[-58]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
