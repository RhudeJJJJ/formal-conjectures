/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode037
import Proofs.RadenkovicGutmanD35Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-33],[0]],[[0,0],[0]],[[-495,0],[0,0]],[[0,0],[0,0]],[[-3102,0],[0,0]],[[0,0],[0,0]],[[-10527,0],[0,0]],[[0,0],[0,0]],[[-20988,0],[0,0]],[[0,0],[0,0]],[[-24948,-33],[-33,0]],[[0,0],[0,0]],[[-16962,-264],[-264,0]],[[0,0],[0,0]],[[-5511,-726],[-726,0]],[[0,0],[0,0]],[[-99,-792],[-792,0]],[[0,0],[0,0]],[[297,-297],[-297,0]],[[0],[0,0]],[[0],[0,-33]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
