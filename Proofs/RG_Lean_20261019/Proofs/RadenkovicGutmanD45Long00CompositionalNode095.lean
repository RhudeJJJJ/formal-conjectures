/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode093
import Proofs.RadenkovicGutmanD45Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,2025]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-18225],[0,-36450,60210],[-18225,60210,90]],[[0,0,0],[0,0,0],[0,0]],[[-164025,-606285,219915],[-606285,1159110,201780],[219915,201780]],[[0,0,0],[0,0,0],[0,0]],[[-7530570,1609875,1842345],[1609875,8126730,220140],[1842345,220140]],[[0,0,0],[0,0,0],[0,0]],[[-40064625,43362945,5213970],[43362945,21637530,91800],[5213970,91800]],[[0,0,0],[0,0,0],[0,0]],[[51273000,213080040,7613820],[213080040,30398580,13410],[7613820,13410]],[[0,0,0],[0,0,0],[0,0]],[[1192737285,545406885,6433020],[545406885,24946380,180],[6433020,180]],[[0,0,0],[0,0],[0]],[[5388700680,873220635,3252195],[873220635,12324330],[3252195]],[[0,0,0],[0,0],[0]],[[13931797590,940791600,970830],[940791600,3611970],[970830]],[[0,0,0],[0,0],[0]],[[24315400530,705487725,158895],[705487725,582930],[158895]],[[0,0,0],[0,0],[0]],[[30593637360,372892995,11385],[372892995,41490],[11385]],[[0,0,0],[0,0],[0]],[[28683851760,138450150,90],[138450150,360],[90]],[[0,0],[0]],[[20391806610,35370675],[35370675]],[[0,0],[0]],[[11075650830,5937255],[5937255]],[[0,0],[0]],[[4595073165,594765],[594765]],[[0,0],[0]],[[1444818240,28080],[28080]],[[0,0],[0]],[[338444730,180],[180]],[[0]],[[57284190]],[[0]],[[6640335]],[[0]],[[476370]],[[0]],[[16695]],[[0]],[[90]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
