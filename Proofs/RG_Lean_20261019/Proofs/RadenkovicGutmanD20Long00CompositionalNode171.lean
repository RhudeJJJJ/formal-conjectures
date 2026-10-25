/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode030
import Proofs.RadenkovicGutmanD20Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[40],[0]],[[0,0],[0]],[[600,0],[0]],[[0,0],[0]],[[3760,0],[0]],[[0,0],[0]],[[12760,0],[0]],[[0,0],[0]],[[25440,0],[0]],[[0,0],[0]],[[30280,20],[20]],[[0,0],[0]],[[20880,140],[140]],[[0,0],[0]],[[7560,320],[320]],[[0,0],[0]],[[1080,260],[260]],[[0,0],[0]],[[0,60],[60]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
