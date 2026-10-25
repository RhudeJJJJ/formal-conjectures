/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode036
import Proofs.RadenkovicGutmanD39Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-74]],[[0,0],[0]],[[738,-666],[-666]],[[0,0],[0]],[[402,-1776],[-1776]],[[0,0],[0]],[[-10238,-1628],[-1628]],[[0,0],[0]],[[-34372,-592],[-592]],[[0,0],[0]],[[-52392,-74],[-74]],[[0]],[[-45064]],[[0]],[[-22958]],[[0]],[[-6844]],[[0]],[[-1102]],[[0]],[[-74]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
