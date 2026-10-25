/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode079
import Proofs.RadenkovicGutmanD28Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-42336,0],[-42336,-7056,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-698544,-613872,0],[-613872,-61152,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11409552,-3782016,0],[-3782016,-207760,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-82893888,-13104560,0],[-13104560,-359072,0],[0,0]],[[0,0,0],[0,0],[0]],[[-356128080,-28562688,0],[-28562688,-348096],[0]],[[0,0,0],[0,0],[0]],[[-1015381136,-41565328,0],[-41565328,-196000],[0]],[[0,0,0],[0,0],[0]],[[-2044494816,-41799744,0],[-41799744,-63504],[0]],[[0,0,0],[0,0],[0]],[[-3019274944,-29594432,0],[-29594432,-10976],[0]],[[0,0,0],[0,0],[0]],[[-3349984176,-14841120,0],[-14841120,-784],[0]],[[0,0],[0]],[[-2835049056,-5236336],[-5236336]],[[0,0],[0]],[[-1845355680,-1270080],[-1270080]],[[0,0],[0]],[[-926192512,-201488],[-201488]],[[0,0],[0]],[[-357274288,-18816],[-18816]],[[0,0],[0]],[[-104865488,-784],[-784]],[[0]],[[-22979040]],[[0]],[[-3637760]],[[0]],[[-392784]],[[0]],[[-25872]],[[0]],[[-784]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
