/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode164
import Proofs.RadenkovicGutmanD39Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-74],[0]],[[0,0],[0]],[[-1102,0],[0,0]],[[0,0],[0,0]],[[-6844,0],[0,0]],[[0,0],[0,0]],[[-22958,0],[0,0]],[[0,0],[0,0]],[[-45064,0],[0,0]],[[0,0],[0,0]],[[-52392,-74],[-74,0]],[[0,0],[0,0]],[[-34372,-592],[-592,0]],[[0,0],[0,0]],[[-10238,-1628],[-1628,0]],[[0,0],[0,0]],[[402,-1776],[-1776,0]],[[0,0],[0,0]],[[738,-666],[-666,0]],[[0],[0,0]],[[0],[0,-74]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
