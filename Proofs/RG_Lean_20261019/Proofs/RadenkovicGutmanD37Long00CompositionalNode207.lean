/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode065
import Proofs.RadenkovicGutmanD37Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-145,0],[0,0]],[[0,0],[0,0]],[[-2057,0],[0,0]],[[0,0],[0,0]],[[-13394,0],[0,0]],[[0,0],[0,0]],[[-48781,0],[0,0]],[[0,0],[0,0]],[[-106592,-2],[-2,0]],[[0,0],[0,0]],[[-141832,-127],[-127,0]],[[0,0],[0,0]],[[-111950,-858],[-858,0]],[[0,0],[0,0]],[[-48307,-2046],[-2046,0]],[[0,0],[0,0]],[[-9231,-1868],[-1868,0]],[[0,0],[0,0]],[[-333,-555],[-555,-2]],[[0],[0,0]],[[0],[0,-37]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
