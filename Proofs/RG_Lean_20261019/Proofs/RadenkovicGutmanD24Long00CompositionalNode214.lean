/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode030
import Proofs.RadenkovicGutmanD24Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[24],[0]],[[0,0],[0]],[[408,0],[0,0]],[[0,0],[0,0]],[[2928,0],[0,0]],[[0,0],[0,0]],[[11544,0],[0,0]],[[0,0],[0,0]],[[27264,0],[0,0]],[[0,0],[0,0]],[[39456,24],[24,0]],[[0,0],[0,0]],[[34320,192],[192,0]],[[0,0],[0,0]],[[16728,528],[528,0]],[[0,0],[0,0]],[[3816,576],[576,0]],[[0,0],[0,0]],[[216,216],[216,0]],[[0],[0,0]],[[0],[0,24]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
