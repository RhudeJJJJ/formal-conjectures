/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode065
import Proofs.RadenkovicGutmanD42Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-42]],[[0,0],[0,0]],[[-378,-630],[-630,-2]],[[0,0],[0]],[[-10476,-2118],[-2118]],[[0,0],[0]],[[-54792,-2316],[-2316]],[[0,0],[0]],[[-126890,-968],[-968]],[[0,0],[0]],[[-160612,-142],[-142]],[[0,0],[0]],[[-120552,-2],[-2]],[[0]],[[-55066]],[[0]],[[-15074]],[[0]],[[-2302]],[[0]],[[-160]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
