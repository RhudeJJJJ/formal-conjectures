/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode174
import Proofs.RadenkovicGutmanD39Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-74],[0]],[[0,0],[0]],[[-1258,0],[0,0]],[[0,0],[0,0]],[[-9028,0],[0,0]],[[0,0],[0,0]],[[-35594,0],[0,0]],[[0,0],[0,0]],[[-84064,0],[0,0]],[[0,0],[0,0]],[[-121656,-74],[-74,0]],[[0,0],[0,0]],[[-105820,-592],[-592,0]],[[0,0],[0,0]],[[-51578,-1628],[-1628,0]],[[0,0],[0,0]],[[-11766,-1776],[-1776,0]],[[0,0],[0,0]],[[-666,-666],[-666,0]],[[0],[0,0]],[[0],[0,-74]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
