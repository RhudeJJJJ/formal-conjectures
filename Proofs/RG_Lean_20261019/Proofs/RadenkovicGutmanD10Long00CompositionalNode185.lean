/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode184
import Proofs.RadenkovicGutmanD10Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[10,0],[0]],[[0,0],[0]],[[160,0],[0]],[[0,0],[0]],[[1070,0],[0]],[[0,0],[0]],[[3880,0],[0]],[[0,0],[0]],[[8280,0],[0]],[[0,0],[0]],[[10560,10],[10]],[[0,0],[0]],[[7790,70],[70]],[[0,0],[0]],[[3000,160],[160]],[[0,0],[0]],[[450,130],[130]],[[0,0],[0]],[[0,30],[30]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
