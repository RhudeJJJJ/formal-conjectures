/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode034
import Proofs.RadenkovicGutmanD29Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-58],[0]],[[0,0],[0]],[[-870,0],[0]],[[0,0],[0]],[[-5452,0],[0]],[[0,0],[0]],[[-18502,0],[0]],[[0,0],[0]],[[-36888,0],[0]],[[0,0],[0]],[[-43906,-29],[-29]],[[0,0],[0]],[[-30276,-203],[-203]],[[0,0],[0]],[[-10962,-464],[-464]],[[0,0],[0]],[[-1566,-377],[-377]],[[0,0],[0]],[[0,-87],[-87]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
