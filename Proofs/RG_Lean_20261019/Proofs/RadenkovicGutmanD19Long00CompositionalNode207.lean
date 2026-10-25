/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode065
import Proofs.RadenkovicGutmanD19Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-91,0],[0,0]],[[0,0],[0,0]],[[-1175,0],[0,0]],[[0,0],[0,0]],[[-7346,0],[0,0]],[[0,0],[0,0]],[[-26155,0],[0,0]],[[0,0],[0,0]],[[-56336,-2],[-2,0]],[[0,0],[0,0]],[[-74224,-73],[-73,0]],[[0,0],[0,0]],[[-58166,-462],[-462,0]],[[0,0],[0,0]],[[-24961,-1074],[-1074,0]],[[0,0],[0,0]],[[-4749,-968],[-968,0]],[[0,0],[0,0]],[[-171,-285],[-285,-2]],[[0],[0,0]],[[0],[0,-19]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
