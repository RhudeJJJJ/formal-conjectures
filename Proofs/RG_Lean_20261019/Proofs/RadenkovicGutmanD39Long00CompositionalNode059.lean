/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode058
import Proofs.RadenkovicGutmanD39Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-74]],[[0,0],[0]],[[-666,-666],[-666]],[[0,0],[0]],[[-11766,-1776],[-1776]],[[0,0],[0]],[[-51578,-1628],[-1628]],[[0,0],[0]],[[-105820,-592],[-592]],[[0,0],[0]],[[-121656,-74],[-74]],[[0]],[[-84064]],[[0]],[[-35594]],[[0]],[[-9028]],[[0]],[[-1258]],[[0]],[[-74]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
