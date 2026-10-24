/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode033
import Proofs.RadenkovicGutmanD2Long00CompositionalNode168
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e033 e168
noncomputable def p214 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-60,0],[0]],[[0,0],[0]],[[-376,0],[0]],[[0,0],[0]],[[-1276,0],[0]],[[0,0],[0]],[[-2544,0],[0]],[[0,0],[0]],[[-3028,-2],[-2]],[[0,0],[0]],[[-2088,-14],[-14]],[[0,0],[0]],[[-756,-32],[-32]],[[0,0],[0]],[[-108,-26],[-26]],[[0,0],[0]],[[0,-6],[-6]]]
theorem step214 : p214=NestedArithmetic.mul p033 p168 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e033 e168 p033 p168 p214 rfl h033 h168 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
