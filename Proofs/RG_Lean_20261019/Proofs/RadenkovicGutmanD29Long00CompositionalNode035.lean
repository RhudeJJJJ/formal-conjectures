/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode034
import Proofs.RadenkovicGutmanD29Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-87],[-87]],[[0,0],[0]],[[-1566,-377],[-377]],[[0,0],[0]],[[-10962,-464],[-464]],[[0,0],[0]],[[-30276,-203],[-203]],[[0,0],[0]],[[-43906,-29],[-29]],[[0]],[[-36888]],[[0]],[[-18502]],[[0]],[[-5452]],[[0]],[[-870]],[[0]],[[-58]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
