/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode030
import Proofs.RadenkovicGutmanD10Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[10],[0]],[[0,0],[0]],[[170,0],[0,0]],[[0,0],[0,0]],[[1220,0],[0,0]],[[0,0],[0,0]],[[4810,0],[0,0]],[[0,0],[0,0]],[[11360,0],[0,0]],[[0,0],[0,0]],[[16440,10],[10,0]],[[0,0],[0,0]],[[14300,80],[80,0]],[[0,0],[0,0]],[[6970,220],[220,0]],[[0,0],[0,0]],[[1590,240],[240,0]],[[0,0],[0,0]],[[90,90],[90,0]],[[0],[0,0]],[[0],[0,10]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
