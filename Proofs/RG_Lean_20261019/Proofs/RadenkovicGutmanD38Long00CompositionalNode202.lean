/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode191
import Proofs.RadenkovicGutmanD38Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[72,0],[0,0]],[[0,0],[0,0]],[[890,0],[0,0]],[[0,0],[0,0]],[[5598,0],[0,0]],[[0,0],[0,0]],[[20550,0],[0,0]],[[0,0],[0,0]],[[46456,2],[2,0]],[[0,0],[0,0]],[[65332,54],[54,0]],[[0,0],[0,0]],[[55734,348],[348,0]],[[0,0],[0,0]],[[26804,884],[884,0]],[[0,0],[0,0]],[[6060,930],[930,0]],[[0,0],[0,0]],[[342,342],[342,2]],[[0],[0,0]],[[0],[0,38]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
