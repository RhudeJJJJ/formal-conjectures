/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode064
import Proofs.RadenkovicGutmanD4Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e065 : NestedArithmetic.Expr 3 := .times e064 e063
noncomputable def p065 : NestedHorner.Poly 3 := [[[0],[0,-4]],[[0,0],[0,0]],[[-36,-60],[-60,-2]],[[0,0],[0]],[[-1014,-218],[-218]],[[0,0],[0]],[[-5506,-264],[-264]],[[0,0],[0]],[[-13346,-132],[-132]],[[0,0],[0]],[[-17884,-28],[-28]],[[0,0],[0]],[[-14456,-2],[-2]],[[0]],[[-7300]],[[0]],[[-2306]],[[0]],[[-440]],[[0]],[[-46]],[[0]],[[-2]]]
theorem step065 : p065=NestedArithmetic.mul p064 p063 := by decide +kernel
#print axioms step065
theorem h065 : NestedArithmetic.compile e065=p065 := StagedExprCompile.compile_times e065 e064 e063 p064 p063 p065 rfl h064 h063 step065
#print axioms h065
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
