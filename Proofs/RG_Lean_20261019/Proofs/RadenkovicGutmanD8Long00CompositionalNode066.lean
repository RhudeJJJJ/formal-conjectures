/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode065
import Proofs.RadenkovicGutmanD8Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-8]],[[0,0],[0,0]],[[-72,-120],[-120,-2]],[[0,0],[0]],[[-2010,-418],[-418]],[[0,0],[0]],[[-10694,-480],[-480]],[[0,0],[0]],[[-25298,-220],[-220]],[[0,0],[0]],[[-32908,-40],[-40]],[[0,0],[0]],[[-25624,-2],[-2]],[[0]],[[-12328]],[[0]],[[-3650]],[[0]],[[-636]],[[0]],[[-58]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
