/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode065
import Proofs.RadenkovicGutmanD32Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-32]],[[0,0],[0,0]],[[-288,-480],[-480,-2]],[[0,0],[0]],[[-7986,-1618],[-1618]],[[0,0],[0]],[[-41822,-1776],[-1776]],[[0,0],[0]],[[-97010,-748],[-748]],[[0,0],[0]],[[-123052,-112],[-112]],[[0,0],[0]],[[-92632,-2],[-2]],[[0]],[[-42496]],[[0]],[[-11714]],[[0]],[[-1812]],[[0]],[[-130]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
