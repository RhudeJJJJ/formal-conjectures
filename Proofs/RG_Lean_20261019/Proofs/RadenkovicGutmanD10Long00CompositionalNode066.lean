/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode065
import Proofs.RadenkovicGutmanD10Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-10]],[[0,0],[0,0]],[[-90,-150],[-150,-2]],[[0,0],[0]],[[-2508,-518],[-518]],[[0,0],[0]],[[-13288,-588],[-588]],[[0,0],[0]],[[-31274,-264],[-264]],[[0,0],[0]],[[-40420,-46],[-46]],[[0,0],[0]],[[-31208,-2],[-2]],[[0]],[[-14842]],[[0]],[[-4322]],[[0]],[[-734]],[[0]],[[-64]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
