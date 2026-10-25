/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode171
import Proofs.RadenkovicGutmanD20Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[40,0],[0]],[[0,0],[0]],[[600,0],[0]],[[0,0],[0]],[[3760,0],[0]],[[0,0],[0]],[[12760,0],[0]],[[0,0],[0]],[[25440,0],[0]],[[0,0],[0]],[[30280,20],[20]],[[0,0],[0]],[[20880,140],[140]],[[0,0],[0]],[[7560,320],[320]],[[0,0],[0]],[[1080,260],[260]],[[0,0],[0]],[[0,60],[60]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
