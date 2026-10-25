/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode093
import Proofs.RadenkovicGutmanD35Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1225]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-11025],[0,-22050,36330],[-11025,36330,70]],[[0,0,0],[0,0,0],[0,0]],[[-99225,-367605,132195],[-367605,697830,121940],[132195,121940]],[[0,0,0],[0,0,0],[0,0]],[[-4571910,940275,1109885],[940275,4897690,133420],[1109885,133420]],[[0,0,0],[0,0,0],[0,0]],[[-24631425,25974585,3144610],[25974585,13051290,56000],[3144610,56000]],[[0,0,0],[0,0,0],[0,0]],[[27617100,127973720,4597460],[127973720,18355540,8330],[4597460,8330]],[[0,0,0],[0,0,0],[0,0]],[[705662405,327998405,3890460],[327998405,15086540,140],[3890460,140]],[[0,0,0],[0,0],[0]],[[3212792940,525685755,1971235],[525685755,7470890],[1971235]],[[0,0,0],[0,0],[0]],[[8332052470,566948200,590590],[566948200,2198210],[590590]],[[0,0,0],[0,0],[0]],[[14569108890,425643925,97335],[425643925,357490],[97335]],[[0,0,0],[0,0],[0]],[[18356320080,225303435,7105],[225303435,25970],[7105]],[[0,0,0],[0,0],[0]],[[17231207280,83812750,70],[83812750,280],[70]],[[0,0],[0]],[[12264292530,21471275],[21471275]],[[0,0],[0]],[[6669526990,3620015],[3620015]],[[0,0],[0]],[[2770976845,365645],[365645]],[[0,0],[0]],[[872777220,17640],[17640]],[[0,0],[0]],[[204907290,140],[140]],[[0]],[[34792870]],[[0]],[[4053455]],[[0]],[[293510]],[[0]],[[10535]],[[0]],[[70]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
