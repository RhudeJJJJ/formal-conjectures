/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode119
import Proofs.RadenkovicGutmanD39Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-74],[0]],[[0,0],[0]],[[-1102,0],[0,0]],[[0,0],[0,0]],[[-6844,0],[0,0]],[[0,0],[0,0]],[[-22958,0],[0,0]],[[0,0],[0,0]],[[-45064,0],[0,0]],[[0,0],[0,0]],[[-52392,-74],[-74,0]],[[0,0],[0,0]],[[-34372,-592],[-592,0]],[[0,0],[0,0]],[[-10238,-1628],[-1628,0]],[[0,0],[0,0]],[[402,-1776],[-1776,0]],[[0,0],[0,0]],[[738,-666],[-666,0]],[[0],[0,0]],[[0],[0,-74]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
