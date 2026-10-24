/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode033
import Proofs.RadenkovicGutmanD2Long00CompositionalNode054
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e055 : NestedArithmetic.Expr 3 := .times e033 e054
noncomputable def p055 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-6],[-6]],[[0,0],[0]],[[-90,-26],[-26]],[[0,0],[0]],[[-600,-32],[-32]],[[0,0],[0]],[[-1558,-14],[-14]],[[0,0],[0]],[[-2112,-2],[-2]],[[0]],[[-1656]],[[0]],[[-776]],[[0]],[[-214]],[[0]],[[-32]],[[0]],[[-2]]]
theorem step055 : p055=NestedArithmetic.mul p033 p054 := by decide +kernel
#print axioms step055
theorem h055 : NestedArithmetic.compile e055=p055 := StagedExprCompile.compile_times e055 e033 e054 p033 p054 p055 rfl h033 h054 step055
#print axioms h055
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
