/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode043
import Proofs.RadenkovicGutmanD7Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-147],[0,-147,70]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-1323,-2205],[-1323,-7560,1001],[-2205,1001,20]],[[0,0,0],[0,0,0],[0,0]],[[-34020,-93744,-7833],[-93744,-21816,4574],[-7833,4574]],[[0,0,0],[0,0,0],[0,0]],[[-1155060,-729954,4126],[-729954,41436,5713],[4126,5713]],[[0,0,0],[0,0,0],[0,0]],[[-11268774,-2478676,60475],[-2478676,264680,2833],[60475,2833]],[[0,0,0],[0,0,0],[0,0]],[[-56730204,-4425870,124146],[-4425870,487296,586],[124146,586]],[[0,0,0],[0,0,0],[0,0]],[[-177300696,-3754258,126025],[-3754258,469836,40],[126025,40]],[[0,0,0],[0,0],[0]],[[-374210708,638860,73370],[638860,265820],[73370]],[[0,0,0],[0,0],[0]],[[-555744196,5453767,25297],[5453767,90512],[25297]],[[0,0,0],[0,0],[0]],[[-588742722,6805379,5023],[6805379,18048],[5023]],[[0,0,0],[0,0],[0]],[[-437692630,4816603,516],[4816603,1908],[516]],[[0,0,0],[0,0],[0]],[[-210121394,2218692,20],[2218692,80],[20]],[[0,0],[0]],[[-40838984,685769],[685769]],[[0,0],[0]],[[25770964,140574],[140574]],[[0,0],[0]],[[27895316,18179],[18179]],[[0,0],[0]],[[13769112,1322],[1322]],[[0,0],[0]],[[4397500,40],[40]],[[0]],[[964886]],[[0]],[[144718]],[[0]],[[14146]],[[0]],[[806]],[[0]],[[20]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
