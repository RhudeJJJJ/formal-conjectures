/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode065
import Proofs.RadenkovicGutmanD42Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-160,0],[0,0]],[[0,0],[0,0]],[[-2302,0],[0,0]],[[0,0],[0,0]],[[-15074,0],[0,0]],[[0,0],[0,0]],[[-55066,0],[0,0]],[[0,0],[0,0]],[[-120552,-2],[-2,0]],[[0,0],[0,0]],[[-160612,-142],[-142,0]],[[0,0],[0,0]],[[-126890,-968],[-968,0]],[[0,0],[0,0]],[[-54792,-2316],[-2316,0]],[[0,0],[0,0]],[[-10476,-2118],[-2118,0]],[[0,0],[0,0]],[[-378,-630],[-630,-2]],[[0],[0,0]],[[0],[0,-42]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
