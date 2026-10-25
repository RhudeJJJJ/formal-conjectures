/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode065
import Proofs.RadenkovicGutmanD36Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-142,0],[0,0]],[[0,0],[0,0]],[[-2008,0],[0,0]],[[0,0],[0,0]],[[-13058,0],[0,0]],[[0,0],[0,0]],[[-47524,0],[0,0]],[[0,0],[0,0]],[[-103800,-2],[-2,0]],[[0,0],[0,0]],[[-138076,-124],[-124,0]],[[0,0],[0,0]],[[-108962,-836],[-836,0]],[[0,0],[0,0]],[[-47010,-1992],[-1992,0]],[[0,0],[0,0]],[[-8982,-1818],[-1818,0]],[[0,0],[0,0]],[[-324,-540],[-540,-2]],[[0],[0,0]],[[0],[0,-36]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
