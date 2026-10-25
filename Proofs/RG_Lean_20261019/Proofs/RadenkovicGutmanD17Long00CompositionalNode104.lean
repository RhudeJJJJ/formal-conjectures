/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode092
import Proofs.RadenkovicGutmanD17Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1224,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11016,-11016,0],[-11016,-10302,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-287334,-122094,0],[-122094,-33388,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2791638,-574668,0],[-574668,-53278,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14719008,-1517250,0],[-1517250,-44812,0],[0,0]],[[0,0,0],[0,0],[0]],[[-48890062,-2500156,0],[-2500156,-18904],[0]],[[0,0,0],[0,0],[0]],[[-110501802,-2695146,0],[-2695146,-2516],[0]],[[0,0,0],[0,0],[0]],[[-177631572,-1921816,0],[-1921816,850],[0]],[[0,0,0],[0,0],[0]],[[-208272032,-880396,0],[-880396,340],[0]],[[0,0,0],[0,0],[0]],[[-180180178,-227936,0],[-227936,34],[0]],[[0,0],[0]],[[-114812084,-11866],[-11866]],[[0,0],[0]],[[-52785748,12580],[12580]],[[0,0],[0]],[[-16449880,4318],[4318]],[[0,0],[0]],[[-2758386,612],[612]],[[0,0],[0]],[[177854,34],[34]],[[0]],[[244188]],[[0]],[[69768]],[[0]],[[10778]],[[0]],[[918]],[[0]],[[34]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
