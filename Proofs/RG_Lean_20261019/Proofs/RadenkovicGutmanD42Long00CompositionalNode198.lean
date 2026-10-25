/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode197
import Proofs.RadenkovicGutmanD42Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[240,0],[0,0]],[[0,0],[0,0]],[[3338,0],[0,0]],[[0,0],[0,0]],[[20378,0],[0,0]],[[0,0],[0,0]],[[68262,0],[0,0]],[[0,0],[0,0]],[[135072,2],[2,0]],[[0,0],[0,0]],[[159956,142],[142,0]],[[0,0],[0,0]],[[109618,968],[968,0]],[[0,0],[0,0]],[[38772,2316],[2316,0]],[[0,0],[0,0]],[[4644,2118],[2118,0]],[[0,0],[0,0]],[[-378,630],[630,2]],[[0],[0,0]],[[0],[0,42]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
