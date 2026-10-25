/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode177
import Proofs.RadenkovicGutmanD39Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-74],[0]],[[0,0],[0]],[[-1258,0],[0,0]],[[0,0],[0,0]],[[-9028,0],[0,0]],[[0,0],[0,0]],[[-35594,0],[0,0]],[[0,0],[0,0]],[[-84064,0],[0,0]],[[0,0],[0,0]],[[-121656,-74],[-74,0]],[[0,0],[0,0]],[[-105820,-592],[-592,0]],[[0,0],[0,0]],[[-51578,-1628],[-1628,0]],[[0,0],[0,0]],[[-11766,-1776],[-1776,0]],[[0,0],[0,0]],[[-666,-666],[-666,0]],[[0],[0,0]],[[0],[0,-74]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
