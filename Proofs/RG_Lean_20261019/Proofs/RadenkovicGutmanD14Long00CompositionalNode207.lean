/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode065
import Proofs.RadenkovicGutmanD14Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-76,0],[0,0]],[[0,0],[0,0]],[[-930,0],[0,0]],[[0,0],[0,0]],[[-5666,0],[0,0]],[[0,0],[0,0]],[[-19870,0],[0,0]],[[0,0],[0,0]],[[-42376,-2],[-2,0]],[[0,0],[0,0]],[[-55444,-58],[-58,0]],[[0,0],[0,0]],[[-43226,-352],[-352,0]],[[0,0],[0,0]],[[-18476,-804],[-804,0]],[[0,0],[0,0]],[[-3504,-718],[-718,0]],[[0,0],[0,0]],[[-126,-210],[-210,-2]],[[0],[0,0]],[[0],[0,-14]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
