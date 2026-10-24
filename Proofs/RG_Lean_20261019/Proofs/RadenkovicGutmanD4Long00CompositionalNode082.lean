/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode069
import Proofs.RadenkovicGutmanD4Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e082 : NestedArithmetic.Expr 3 := .plus e069 e081
noncomputable def p082 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,96],[0,96,32]],[[0,0,0],[0,0,0],[0,0,0]],[[0,864,1440],[864,4320,1088],[1440,1088,4]],[[0,0,0],[0,0,0],[0,0]],[[10368,51840,14496],[51840,45432,2536],[14496,2536]],[[0,0,0],[0,0,0],[0,0]],[[440532,551736,53860],[551736,172416,2336],[53860,2336]],[[0,0,0],[0,0,0],[0,0]],[[5103432,2672312,103072],[2672312,336888,944],[103072,944]],[[0,0,0],[0,0,0],[0,0]],[[29870124,7507528,115280],[7507528,386416,160],[115280,160]],[[0,0,0],[0,0,0],[0,0]],[[108026840,13646912,79712],[13646912,275296,8],[79712,8]],[[0,0,0],[0,0],[0]],[[266267460,17019176,34744],[17019176,124016],[34744]],[[0,0,0],[0,0],[0]],[[473154096,15050424,9440],[15050424,34872],[9440]],[[0,0,0],[0,0],[0]],[[627657176,9602736,1520],[9602736,5808],[1520]],[[0,0,0],[0,0],[0]],[[635517016,4445600,128],[4445600,504],[128]],[[0,0,0],[0,0],[0]],[[497978592,1485576,4],[1485576,16],[4]],[[0,0],[0]],[[304257952,352008],[352008]],[[0,0],[0]],[[145276320,57064],[57064]],[[0,0],[0]],[[54054600,5920],[5920]],[[0,0],[0]],[[15540900,344],[344]],[[0,0],[0]],[[3399184,8],[8]],[[0]],[[551352]],[[0]],[[63624]],[[0]],[[4868]],[[0]],[[216]],[[0]],[[4]]]
theorem step082 : p082=NestedHorner.add p069 p081 := by decide +kernel
#print axioms step082
theorem h082 : NestedArithmetic.compile e082=p082 := StagedExprCompile.compile_plus e082 e069 e081 p069 p081 p082 rfl h069 h081 step082
#print axioms h082
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
