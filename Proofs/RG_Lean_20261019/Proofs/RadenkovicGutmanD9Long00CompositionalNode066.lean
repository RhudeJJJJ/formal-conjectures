/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode065
import Proofs.RadenkovicGutmanD9Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-9]],[[0,0],[0,0]],[[-81,-135],[-135,-2]],[[0,0],[0]],[[-2259,-468],[-468]],[[0,0],[0]],[[-11991,-534],[-534]],[[0,0],[0]],[[-28286,-242],[-242]],[[0,0],[0]],[[-36664,-43],[-43]],[[0,0],[0]],[[-28416,-2],[-2]],[[0]],[[-13585]],[[0]],[[-3986]],[[0]],[[-685]],[[0]],[[-61]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
