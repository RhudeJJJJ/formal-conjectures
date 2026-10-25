/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode174
import Proofs.RadenkovicGutmanD14Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-408,0],[0,0]],[[0,0],[0,0]],[[-2928,0],[0,0]],[[0,0],[0,0]],[[-11544,0],[0,0]],[[0,0],[0,0]],[[-27264,0],[0,0]],[[0,0],[0,0]],[[-39456,-24],[-24,0]],[[0,0],[0,0]],[[-34320,-192],[-192,0]],[[0,0],[0,0]],[[-16728,-528],[-528,0]],[[0,0],[0,0]],[[-3816,-576],[-576,0]],[[0,0],[0,0]],[[-216,-216],[-216,0]],[[0],[0,0]],[[0],[0,-24]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
