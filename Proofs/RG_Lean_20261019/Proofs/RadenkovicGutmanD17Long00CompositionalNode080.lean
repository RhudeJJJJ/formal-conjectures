/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode035
import Proofs.RadenkovicGutmanD17Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-867],[0,-867]],[[0,0,0],[0,0,0],[0,0]],[[0,-7803,-7803],[-7803,-31212,-3757],[-7803,-3757]],[[0,0,0],[0,0,0],[0,0]],[[-140454,-312120,-54621],[-312120,-218484,-4624],[-54621,-4624]],[[0,0,0],[0,0,0],[0,0]],[[-3464532,-2601000,-150858],[-2601000,-603432,-2023],[-150858,-2023]],[[0,0,0],[0,0,0],[0,0]],[[-30962304,-10292446,-218773],[-10292446,-875092,-289],[-218773,-289]],[[0,0,0],[0,0],[0]],[[-150369012,-24052314,-183804],[-24052314,-735216],[-183804]],[[0,0,0],[0,0],[0]],[[-465046662,-36566592,-92191],[-36566592,-368764],[-92191]],[[0,0,0],[0,0],[0]],[[-993854816,-38012170,-27166],[-38012170,-108664],[-27166]],[[0,0,0],[0,0],[0]],[[-1539345784,-27708453,-4335],[-27708453,-17340],[-4335]],[[0,0,0],[0,0],[0]],[[-1779434846,-14287293,-289],[-14287293,-1156],[-289]],[[0,0],[0]],[[-1563037426,-5181481],[-5181481]],[[0,0],[0]],[[-1053698046,-1291830],[-1291830]],[[0,0],[0]],[[-547019200,-210681],[-210681]],[[0,0],[0]],[[-218077088,-20230],[-20230]],[[0,0],[0]],[[-66114530,-867],[-867]],[[0]],[[-14957484]],[[0]],[[-2443784]],[[0]],[[-272238]],[[0]],[[-18496]],[[0]],[[-578]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
