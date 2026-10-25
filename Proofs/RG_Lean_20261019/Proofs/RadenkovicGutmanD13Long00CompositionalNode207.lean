/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode065
import Proofs.RadenkovicGutmanD13Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-73,0],[0,0]],[[0,0],[0,0]],[[-881,0],[0,0]],[[0,0],[0,0]],[[-5330,0],[0,0]],[[0,0],[0,0]],[[-18613,0],[0,0]],[[0,0],[0,0]],[[-39584,-2],[-2,0]],[[0,0],[0,0]],[[-51688,-55],[-55,0]],[[0,0],[0,0]],[[-40238,-330],[-330,0]],[[0,0],[0,0]],[[-17179,-750],[-750,0]],[[0,0],[0,0]],[[-3255,-668],[-668,0]],[[0,0],[0,0]],[[-117,-195],[-195,-2]],[[0],[0,0]],[[0],[0,-13]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
