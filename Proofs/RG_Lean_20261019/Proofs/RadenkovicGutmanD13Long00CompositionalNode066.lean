/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode065
import Proofs.RadenkovicGutmanD13Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-13]],[[0,0],[0,0]],[[-117,-195],[-195,-2]],[[0,0],[0]],[[-3255,-668],[-668]],[[0,0],[0]],[[-17179,-750],[-750]],[[0,0],[0]],[[-40238,-330],[-330]],[[0,0],[0]],[[-51688,-55],[-55]],[[0,0],[0]],[[-39584,-2],[-2]],[[0]],[[-18613]],[[0]],[[-5330]],[[0]],[[-881]],[[0]],[[-73]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
