/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode064
import Proofs.RadenkovicGutmanD4Long00CompositionalNode204
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e064 e204
noncomputable def p205 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-46,0],[0,0]],[[0,0],[0,0]],[[-440,0],[0,0]],[[0,0],[0,0]],[[-2306,0],[0,0]],[[0,0],[0,0]],[[-7300,0],[0,0]],[[0,0],[0,0]],[[-14456,-2],[-2,0]],[[0,0],[0,0]],[[-17884,-28],[-28,0]],[[0,0],[0,0]],[[-13346,-132],[-132,0]],[[0,0],[0,0]],[[-5506,-264],[-264,0]],[[0,0],[0,0]],[[-1014,-218],[-218,0]],[[0,0],[0,0]],[[-36,-60],[-60,-2]],[[0],[0,0]],[[0],[0,-4]]]
theorem step205 : p205=NestedArithmetic.mul p064 p204 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e064 e204 p064 p204 p205 rfl h064 h204 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
