/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode113
import Proofs.RadenkovicGutmanD23Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,529]],[[0,0],[0,0,0],[0,0]],[[0,0,4761],[0,0,9522],[4761,9522]],[[0,0,0],[0,0,0],[0,0]],[[42849,85698,84111],[85698,171396,25392],[84111,25392]],[[0,0,0],[0,0,0],[0,0]],[[1513998,1742526,368713],[1742526,914112,23276],[368713,23276]],[[0,0,0],[0,0,0],[0,0]],[[20010483,10883646,756470],[10883646,2056752,8464],[756470,8464]],[[0,0,0],[0,0,0],[0,0]],[[130867194,35091744,869676],[35091744,2539200,1058],[869676,1058]],[[0,0,0],[0,0],[0]],[[513204589,69543398,600944],[69543398,1874776],[600944]],[[0,0,0],[0,0],[0]],[[1341893140,91913750,254449],[91913750,846400],[254449]],[[0,0,0],[0,0],[0]],[[2489760718,84532084,64538],[84532084,228528],[64538]],[[0,0,0],[0,0],[0]],[[3407065762,55244528,8993],[55244528,33856],[8993]],[[0,0,0],[0,0],[0]],[[3523834048,25809910,529],[25809910,2116],[529]],[[0,0],[0]],[[2796463280,8553930],[8553930]],[[0,0],[0]],[[1716583840,1962590],[1962590]],[[0,0],[0]],[[816766478,296240],[296240]],[[0,0],[0]],[[300102229,26450],[26450]],[[0,0],[0]],[[84257004,1058],[1058]],[[0]],[[17726790]],[[0]],[[2703190]],[[0]],[[281957]],[[0]],[[17986]],[[0]],[[529]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
