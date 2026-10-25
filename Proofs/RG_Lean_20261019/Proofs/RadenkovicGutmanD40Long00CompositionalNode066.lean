/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode065
import Proofs.RadenkovicGutmanD40Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-40]],[[0,0],[0,0]],[[-360,-600],[-600,-2]],[[0,0],[0]],[[-9978,-2018],[-2018]],[[0,0],[0]],[[-52198,-2208],[-2208]],[[0,0],[0]],[[-120914,-924],[-924]],[[0,0],[0]],[[-153100,-136],[-136]],[[0,0],[0]],[[-114968,-2],[-2]],[[0]],[[-52552]],[[0]],[[-14402]],[[0]],[[-2204]],[[0]],[[-154]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
