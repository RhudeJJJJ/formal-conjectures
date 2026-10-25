/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode065
import Proofs.RadenkovicGutmanD37Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-37]],[[0,0],[0,0]],[[-333,-555],[-555,-2]],[[0,0],[0]],[[-9231,-1868],[-1868]],[[0,0],[0]],[[-48307,-2046],[-2046]],[[0,0],[0]],[[-111950,-858],[-858]],[[0,0],[0]],[[-141832,-127],[-127]],[[0,0],[0]],[[-106592,-2],[-2]],[[0]],[[-48781]],[[0]],[[-13394]],[[0]],[[-2057]],[[0]],[[-145]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
