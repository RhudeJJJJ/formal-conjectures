/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode177
import Proofs.RadenkovicGutmanD14Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-408,0],[0,0]],[[0,0],[0,0]],[[-2928,0],[0,0]],[[0,0],[0,0]],[[-11544,0],[0,0]],[[0,0],[0,0]],[[-27264,0],[0,0]],[[0,0],[0,0]],[[-39456,-24],[-24,0]],[[0,0],[0,0]],[[-34320,-192],[-192,0]],[[0,0],[0,0]],[[-16728,-528],[-528,0]],[[0,0],[0,0]],[[-3816,-576],[-576,0]],[[0,0],[0,0]],[[-216,-216],[-216,0]],[[0],[0,0]],[[0],[0,-24]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
