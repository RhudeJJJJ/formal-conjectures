/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode177
import Proofs.RadenkovicGutmanD28Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-52],[0]],[[0,0],[0]],[[-884,0],[0,0]],[[0,0],[0,0]],[[-6344,0],[0,0]],[[0,0],[0,0]],[[-25012,0],[0,0]],[[0,0],[0,0]],[[-59072,0],[0,0]],[[0,0],[0,0]],[[-85488,-52],[-52,0]],[[0,0],[0,0]],[[-74360,-416],[-416,0]],[[0,0],[0,0]],[[-36244,-1144],[-1144,0]],[[0,0],[0,0]],[[-8268,-1248],[-1248,0]],[[0,0],[0,0]],[[-468,-468],[-468,0]],[[0],[0,0]],[[0],[0,-52]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
