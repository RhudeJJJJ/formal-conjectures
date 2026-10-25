/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode065
import Proofs.RadenkovicGutmanD22Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-22]],[[0,0],[0,0]],[[-198,-330],[-330,-2]],[[0,0],[0]],[[-5496,-1118],[-1118]],[[0,0],[0]],[[-28852,-1236],[-1236]],[[0,0],[0]],[[-67130,-528],[-528]],[[0,0],[0]],[[-85492,-82],[-82]],[[0,0],[0]],[[-64712,-2],[-2]],[[0]],[[-29926]],[[0]],[[-8354]],[[0]],[[-1322]],[[0]],[[-100]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
