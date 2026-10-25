/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode065
import Proofs.RadenkovicGutmanD40Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-154,0],[0,0]],[[0,0],[0,0]],[[-2204,0],[0,0]],[[0,0],[0,0]],[[-14402,0],[0,0]],[[0,0],[0,0]],[[-52552,0],[0,0]],[[0,0],[0,0]],[[-114968,-2],[-2,0]],[[0,0],[0,0]],[[-153100,-136],[-136,0]],[[0,0],[0,0]],[[-120914,-924],[-924,0]],[[0,0],[0,0]],[[-52198,-2208],[-2208,0]],[[0,0],[0,0]],[[-9978,-2018],[-2018,0]],[[0,0],[0,0]],[[-360,-600],[-600,-2]],[[0],[0,0]],[[0],[0,-40]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
