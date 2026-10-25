/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode151
import Proofs.RadenkovicGutmanD17Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e152 : NestedArithmetic.Expr 3 := .times e151 e122
noncomputable def p152 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[16,0],[0,0]],[[0,0],[0,0]],[[108,0],[0,0]],[[0,0],[0,0]],[[400,0],[0,0]],[[0,0],[0,0]],[[886,0],[0,0]],[[0,0],[0,0]],[[1200,1],[1,0]],[[0,0],[0,0]],[[972,8],[8,0]],[[0,0],[0,0]],[[432,22],[22,0]],[[0,0],[0,0]],[[81,24],[24,0]],[[0,0],[0,0]],[[0,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step152 : p152=NestedArithmetic.mul p151 p122 := by decide +kernel
#print axioms step152
theorem h152 : NestedArithmetic.compile e152=p152 := StagedExprCompile.compile_times e152 e151 e122 p151 p122 p152 rfl h151 h122 step152
#print axioms h152
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
