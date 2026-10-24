/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode043
import Proofs.RadenkovicGutmanD2Long00CompositionalNode031
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e044 : NestedArithmetic.Expr 3 := .times e043 e031
noncomputable def p044 : NestedHorner.Poly 3 := [[[0],[0,2]],[[0,0],[0,0]],[[-18,18],[18,2]],[[0,0],[0]],[[-12,66],[66]],[[0,0],[0]],[[340,92],[92]],[[0,0],[0]],[[1362,60],[60]],[[0,0],[0]],[[2540,18],[18]],[[0,0],[0]],[[2784,2],[2]],[[0]],[[1910]],[[0]],[[826]],[[0]],[[218]],[[0]],[[32]],[[0]],[[2]]]
theorem step044 : p044=NestedArithmetic.mul p043 p031 := by decide +kernel
#print axioms step044
theorem h044 : NestedArithmetic.compile e044=p044 := StagedExprCompile.compile_times e044 e043 e031 p043 p031 p044 rfl h043 h031 step044
#print axioms h044
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
