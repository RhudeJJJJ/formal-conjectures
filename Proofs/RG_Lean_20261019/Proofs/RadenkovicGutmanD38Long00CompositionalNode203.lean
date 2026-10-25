/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode202
import Proofs.RadenkovicGutmanD38Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[72,0],[0,0]],[[0,0],[0,0]],[[890,0],[0,0]],[[0,0],[0,0]],[[5598,0],[0,0]],[[0,0],[0,0]],[[20550,0],[0,0]],[[0,0],[0,0]],[[46456,2],[2,0]],[[0,0],[0,0]],[[65332,54],[54,0]],[[0,0],[0,0]],[[55734,348],[348,0]],[[0,0],[0,0]],[[26804,884],[884,0]],[[0,0],[0,0]],[[6060,930],[930,0]],[[0,0],[0,0]],[[342,342],[342,2]],[[0],[0,0]],[[0],[0,38]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
