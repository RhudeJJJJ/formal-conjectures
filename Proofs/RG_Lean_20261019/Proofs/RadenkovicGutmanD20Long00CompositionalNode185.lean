/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode184
import Proofs.RadenkovicGutmanD20Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[20,0],[0]],[[0,0],[0]],[[320,0],[0]],[[0,0],[0]],[[2140,0],[0]],[[0,0],[0]],[[7760,0],[0]],[[0,0],[0]],[[16560,0],[0]],[[0,0],[0]],[[21120,20],[20]],[[0,0],[0]],[[15580,140],[140]],[[0,0],[0]],[[6000,320],[320]],[[0,0],[0]],[[900,260],[260]],[[0,0],[0]],[[0,60],[60]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
