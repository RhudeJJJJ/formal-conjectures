/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode065
import Proofs.RadenkovicGutmanD19Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-19]],[[0,0],[0,0]],[[-171,-285],[-285,-2]],[[0,0],[0]],[[-4749,-968],[-968]],[[0,0],[0]],[[-24961,-1074],[-1074]],[[0,0],[0]],[[-58166,-462],[-462]],[[0,0],[0]],[[-74224,-73],[-73]],[[0,0],[0]],[[-56336,-2],[-2]],[[0]],[[-26155]],[[0]],[[-7346]],[[0]],[[-1175]],[[0]],[[-91]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
