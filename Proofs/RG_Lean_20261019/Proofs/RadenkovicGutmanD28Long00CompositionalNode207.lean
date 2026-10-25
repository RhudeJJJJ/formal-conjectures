/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode065
import Proofs.RadenkovicGutmanD28Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-118,0],[0,0]],[[0,0],[0,0]],[[-1616,0],[0,0]],[[0,0],[0,0]],[[-10370,0],[0,0]],[[0,0],[0,0]],[[-37468,0],[0,0]],[[0,0],[0,0]],[[-81464,-2],[-2,0]],[[0,0],[0,0]],[[-108028,-100],[-100,0]],[[0,0],[0,0]],[[-85058,-660],[-660,0]],[[0,0],[0,0]],[[-36634,-1560],[-1560,0]],[[0,0],[0,0]],[[-6990,-1418],[-1418,0]],[[0,0],[0,0]],[[-252,-420],[-420,-2]],[[0],[0,0]],[[0],[0,-28]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
