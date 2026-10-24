/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode033
import Proofs.RadenkovicGutmanD2Long00CompositionalNode181
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e215 : NestedArithmetic.Expr 3 := .times e033 e181
noncomputable def p215 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-32,0],[0]],[[0,0],[0]],[[-214,0],[0]],[[0,0],[0]],[[-776,0],[0]],[[0,0],[0]],[[-1656,0],[0]],[[0,0],[0]],[[-2112,-2],[-2]],[[0,0],[0]],[[-1558,-14],[-14]],[[0,0],[0]],[[-600,-32],[-32]],[[0,0],[0]],[[-90,-26],[-26]],[[0,0],[0]],[[0,-6],[-6]]]
theorem step215 : p215=NestedArithmetic.mul p033 p181 := by decide +kernel
#print axioms step215
theorem h215 : NestedArithmetic.compile e215=p215 := StagedExprCompile.compile_times e215 e033 e181 p033 p181 p215 rfl h033 h181 step215
#print axioms h215
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
