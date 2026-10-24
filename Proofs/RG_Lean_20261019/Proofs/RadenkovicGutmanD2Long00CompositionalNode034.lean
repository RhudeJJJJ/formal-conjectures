/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode033
import Proofs.RadenkovicGutmanD2Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e034 : NestedArithmetic.Expr 3 := .times e033 e028
noncomputable def p034 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-6],[-6]],[[0,0],[0]],[[-108,-26],[-26]],[[0,0],[0]],[[-756,-32],[-32]],[[0,0],[0]],[[-2088,-14],[-14]],[[0,0],[0]],[[-3028,-2],[-2]],[[0]],[[-2544]],[[0]],[[-1276]],[[0]],[[-376]],[[0]],[[-60]],[[0]],[[-4]]]
theorem step034 : p034=NestedArithmetic.mul p033 p028 := by decide +kernel
#print axioms step034
theorem h034 : NestedArithmetic.compile e034=p034 := StagedExprCompile.compile_times e034 e033 e028 p033 p028 p034 rfl h033 h028 step034
#print axioms h034
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
