/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode070
import Proofs.RadenkovicGutmanD7Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,168],[0,168,128]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1512,3276],[1512,8856,3200],[3276,3200,4]],[[0,0,0],[0,0,0],[0,0]],[[10368,113724,37752],[113724,114012,7840],[37752,7840]],[[0,0,0],[0,0,0],[0,0]],[[822528,1326960,147376],[1326960,462864,7112],[147376,7112]],[[0,0,0],[0,0,0],[0,0]],[[10897524,6732380,287536],[6732380,928668,2672],[287536,2672]],[[0,0,0],[0,0,0],[0,0]],[[67909668,19399084,322520],[19399084,1071352,376],[322520,376]],[[0,0,0],[0,0,0],[0,0]],[[254551196,35737316,220688],[35737316,755872,8],[220688,8]],[[0,0,0],[0,0],[0]],[[641466912,44803640,93748],[44803640,331760],[93748]],[[0,0,0],[0,0],[0]],[[1155849144,39572160,24272],[39572160,88860],[24272]],[[0,0,0],[0,0],[0]],[[1546056608,25062420,3572],[25062420,13536],[3572]],[[0,0,0],[0,0],[0]],[[1571679580,11438612,248],[11438612,972],[248]],[[0,0,0],[0,0],[0]],[[1231887000,3735732,4],[3735732,16],[4]],[[0,0],[0]],[[750193456,854364],[854364]],[[0,0],[0]],[[355661688,130984],[130984]],[[0,0],[0]],[[130809108,12364],[12364]],[[0,0],[0]],[[36962544,596],[596]],[[0,0],[0]],[[7883464,8],[8]],[[0]],[[1232256]],[[0]],[[134388]],[[0]],[[9368]],[[0]],[[348]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
