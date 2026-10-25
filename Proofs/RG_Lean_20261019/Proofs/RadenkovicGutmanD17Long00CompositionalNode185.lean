/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode184
import Proofs.RadenkovicGutmanD17Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[17,0],[0]],[[0,0],[0]],[[272,0],[0]],[[0,0],[0]],[[1819,0],[0]],[[0,0],[0]],[[6596,0],[0]],[[0,0],[0]],[[14076,0],[0]],[[0,0],[0]],[[17952,17],[17]],[[0,0],[0]],[[13243,119],[119]],[[0,0],[0]],[[5100,272],[272]],[[0,0],[0]],[[765,221],[221]],[[0,0],[0]],[[0,51],[51]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
