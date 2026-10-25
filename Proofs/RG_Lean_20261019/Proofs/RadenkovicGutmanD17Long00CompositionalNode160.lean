/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode159
import Proofs.RadenkovicGutmanD17Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-15],[0]],[[0,0],[0]],[[-225,0],[0,0]],[[0,0],[0,0]],[[-1410,0],[0,0]],[[0,0],[0,0]],[[-4785,0],[0,0]],[[0,0],[0,0]],[[-9540,0],[0,0]],[[0,0],[0,0]],[[-11340,-15],[-15,0]],[[0,0],[0,0]],[[-7710,-120],[-120,0]],[[0,0],[0,0]],[[-2505,-330],[-330,0]],[[0,0],[0,0]],[[-45,-360],[-360,0]],[[0,0],[0,0]],[[135,-135],[-135,0]],[[0],[0,0]],[[0],[0,-15]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
