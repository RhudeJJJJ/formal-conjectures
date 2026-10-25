/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode044
import Proofs.RadenkovicGutmanD20Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,20]],[[0,0],[0,0]],[[180,180],[180,2]],[[0,0],[0]],[[3198,498],[498]],[[0,0],[0]],[[14258,488],[488]],[[0,0],[0]],[[29994,204],[204]],[[0,0],[0]],[[35740,36],[36]],[[0,0],[0]],[[26008,2],[2]],[[0]],[[11892]],[[0]],[[3402]],[[0]],[[584]],[[0]],[[54]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
