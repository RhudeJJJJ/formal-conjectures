/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode177
import Proofs.RadenkovicGutmanD33Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-62],[0]],[[0,0],[0]],[[-1054,0],[0,0]],[[0,0],[0,0]],[[-7564,0],[0,0]],[[0,0],[0,0]],[[-29822,0],[0,0]],[[0,0],[0,0]],[[-70432,0],[0,0]],[[0,0],[0,0]],[[-101928,-62],[-62,0]],[[0,0],[0,0]],[[-88660,-496],[-496,0]],[[0,0],[0,0]],[[-43214,-1364],[-1364,0]],[[0,0],[0,0]],[[-9858,-1488],[-1488,0]],[[0,0],[0,0]],[[-558,-558],[-558,0]],[[0],[0,0]],[[0],[0,-62]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
