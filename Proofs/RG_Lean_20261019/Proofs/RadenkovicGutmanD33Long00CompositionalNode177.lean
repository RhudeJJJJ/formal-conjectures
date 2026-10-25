/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode174
import Proofs.RadenkovicGutmanD33Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-62],[0]],[[0,0],[0]],[[-1054,0],[0,0]],[[0,0],[0,0]],[[-7564,0],[0,0]],[[0,0],[0,0]],[[-29822,0],[0,0]],[[0,0],[0,0]],[[-70432,0],[0,0]],[[0,0],[0,0]],[[-101928,-62],[-62,0]],[[0,0],[0,0]],[[-88660,-496],[-496,0]],[[0,0],[0,0]],[[-43214,-1364],[-1364,0]],[[0,0],[0,0]],[[-9858,-1488],[-1488,0]],[[0,0],[0,0]],[[-558,-558],[-558,0]],[[0],[0,0]],[[0],[0,-62]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
