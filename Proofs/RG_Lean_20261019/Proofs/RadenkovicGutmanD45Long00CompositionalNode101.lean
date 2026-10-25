/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode051
import Proofs.RadenkovicGutmanD45Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,2025]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,48600],[0,48600,90]],[[0,0,0],[0,0,0],[0,0]],[[-164025,109350,273375],[109350,1095120,151470],[273375,151470]],[[0,0,0],[0,0,0],[0,0]],[[-867510,7341030,1647540],[7341030,6604200,158220],[1647540,158220]],[[0,0,0],[0,0,0],[0,0]],[[40115655,60366060,4121280],[60366060,16532820,64710],[4121280,64710]],[[0,0,0],[0,0,0],[0,0]],[[478615230,230725260,5583330],[230725260,22415760,9540],[5583330,9540]],[[0,0,0],[0,0,0],[0,0]],[[2523218715,522369540,4477950],[522369540,17991720,180],[4477950,180]],[[0,0,0],[0,0],[0]],[[8057753190,774134730,2181690],[774134730,8771760],[2181690]],[[0,0,0],[0,0],[0]],[[17476159950,789195600,635400],[789195600,2556180],[635400]],[[0,0,0],[0,0],[0]],[[27283034880,567259290,102870],[567259290,414000],[102870]],[[0,0,0],[0,0],[0]],[[31701148020,289905930,7515],[289905930,30240],[7515]],[[0,0,0],[0,0],[0]],[[27963343080,104766300,90],[104766300,360],[90]],[[0,0],[0]],[[18929958300,26200800],[26200800]],[[0,0],[0]],[[9873779400,4331250],[4331250]],[[0,0],[0]],[[3959029755,431100],[431100]],[[0,0],[0]],[[1209203190,20700],[20700]],[[0,0],[0]],[[276349590,180],[180]],[[0]],[[45824400]],[[0]],[[5228775]],[[0]],[[371970]],[[0]],[[13185]],[[0]],[[90]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
