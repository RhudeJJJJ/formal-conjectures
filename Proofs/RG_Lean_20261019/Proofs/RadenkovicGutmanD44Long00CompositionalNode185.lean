/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode184
import Proofs.RadenkovicGutmanD44Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[44,0],[0]],[[0,0],[0]],[[704,0],[0]],[[0,0],[0]],[[4708,0],[0]],[[0,0],[0]],[[17072,0],[0]],[[0,0],[0]],[[36432,0],[0]],[[0,0],[0]],[[46464,44],[44]],[[0,0],[0]],[[34276,308],[308]],[[0,0],[0]],[[13200,704],[704]],[[0,0],[0]],[[1980,572],[572]],[[0,0],[0]],[[0,132],[132]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
