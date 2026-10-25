/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode058
import Proofs.RadenkovicGutmanD37Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-70]],[[0,0],[0]],[[-630,-630],[-630]],[[0,0],[0]],[[-11130,-1680],[-1680]],[[0,0],[0]],[[-48790,-1540],[-1540]],[[0,0],[0]],[[-100100,-560],[-560]],[[0,0],[0]],[[-115080,-70],[-70]],[[0]],[[-79520]],[[0]],[[-33670]],[[0]],[[-8540]],[[0]],[[-1190]],[[0]],[[-70]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
