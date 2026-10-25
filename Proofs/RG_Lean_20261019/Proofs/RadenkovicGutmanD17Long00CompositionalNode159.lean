/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode037
import Proofs.RadenkovicGutmanD17Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-15],[0]],[[0,0],[0]],[[-225,0],[0,0]],[[0,0],[0,0]],[[-1410,0],[0,0]],[[0,0],[0,0]],[[-4785,0],[0,0]],[[0,0],[0,0]],[[-9540,0],[0,0]],[[0,0],[0,0]],[[-11340,-15],[-15,0]],[[0,0],[0,0]],[[-7710,-120],[-120,0]],[[0,0],[0,0]],[[-2505,-330],[-330,0]],[[0,0],[0,0]],[[-45,-360],[-360,0]],[[0,0],[0,0]],[[135,-135],[-135,0]],[[0],[0,0]],[[0],[0,-15]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
