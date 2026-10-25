/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode112
import Proofs.RadenkovicGutmanD22Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,528],[0,528,1688]],[[0,0,0],[0,0,0],[0,0,0]],[[0,4752,22176],[4752,19296,33200],[22176,33200,4]],[[0,0,0],[0,0,0],[0,0]],[[265032,511056,325752],[511056,701544,86200],[325752,86200]],[[0,0,0],[0,0,0],[0,0]],[[8153028,7819704,1367716],[7819704,3427808,78512],[1367716,78512]],[[0,0,0],[0,0,0],[0,0]],[[95948928,44946392,2754256],[44946392,7487048,28592],[2754256,28592]],[[0,0,0],[0,0,0],[0,0]],[[588093324,139451864,3134240],[139451864,9116496,3616],[3134240,3616]],[[0,0,0],[0,0,0],[0,0]],[[2218163120,270416032,2152448],[270416032,6685344,8],[2152448,8]],[[0,0,0],[0,0],[0]],[[5654432980,352529096,908248],[352529096,3010320],[908248]],[[0,0,0],[0,0],[0]],[[10307179488,321239208,230192],[321239208,813448],[230192]],[[0,0,0],[0,0],[0]],[[13922653176,208609904,32192],[208609904,121168],[32192]],[[0,0,0],[0,0],[0]],[[14257885416,97045152,1928],[97045152,7720],[1928]],[[0,0,0],[0,0],[0]],[[11227345888,32081784,4],[32081784,16],[4]],[[0,0],[0]],[[6849354336,7355704],[7355704]],[[0,0],[0]],[[3242998016,1112360],[1112360]],[[0,0],[0]],[[1187019648,100016],[100016]],[[0,0],[0]],[[332351156,4104],[4104]],[[0,0],[0]],[[69814144,8],[8]],[[0]],[[10646616]],[[0]],[[1113568]],[[0]],[[71668]],[[0]],[[2176]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
