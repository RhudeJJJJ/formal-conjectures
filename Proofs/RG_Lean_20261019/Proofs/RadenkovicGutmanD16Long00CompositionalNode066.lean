/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode065
import Proofs.RadenkovicGutmanD16Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-16]],[[0,0],[0,0]],[[-144,-240],[-240,-2]],[[0,0],[0]],[[-4002,-818],[-818]],[[0,0],[0]],[[-21070,-912],[-912]],[[0,0],[0]],[[-49202,-396],[-396]],[[0,0],[0]],[[-62956,-64],[-64]],[[0,0],[0]],[[-47960,-2],[-2]],[[0]],[[-22384]],[[0]],[[-6338]],[[0]],[[-1028]],[[0]],[[-82]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
