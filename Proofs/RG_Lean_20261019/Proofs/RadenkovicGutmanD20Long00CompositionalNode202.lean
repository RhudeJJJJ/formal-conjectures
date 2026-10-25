/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode191
import Proofs.RadenkovicGutmanD20Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[54,0],[0,0]],[[0,0],[0,0]],[[584,0],[0,0]],[[0,0],[0,0]],[[3402,0],[0,0]],[[0,0],[0,0]],[[11892,0],[0,0]],[[0,0],[0,0]],[[26008,2],[2,0]],[[0,0],[0,0]],[[35740,36],[36,0]],[[0,0],[0,0]],[[29994,204],[204,0]],[[0,0],[0,0]],[[14258,488],[488,0]],[[0,0],[0,0]],[[3198,498],[498,0]],[[0,0],[0,0]],[[180,180],[180,2]],[[0],[0,0]],[[0],[0,20]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
