/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode159
import Proofs.RadenkovicGutmanD35Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-33],[0]],[[0,0],[0]],[[-495,0],[0,0]],[[0,0],[0,0]],[[-3102,0],[0,0]],[[0,0],[0,0]],[[-10527,0],[0,0]],[[0,0],[0,0]],[[-20988,0],[0,0]],[[0,0],[0,0]],[[-24948,-33],[-33,0]],[[0,0],[0,0]],[[-16962,-264],[-264,0]],[[0,0],[0,0]],[[-5511,-726],[-726,0]],[[0,0],[0,0]],[[-99,-792],[-792,0]],[[0,0],[0,0]],[[297,-297],[-297,0]],[[0],[0,0]],[[0],[0,-33]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
