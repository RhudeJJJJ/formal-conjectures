/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode035
import Proofs.RadenkovicGutmanD21Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1323],[0,-1323]],[[0,0,0],[0,0,0],[0,0]],[[0,-11907,-11907],[-11907,-47628,-5733],[-11907,-5733]],[[0,0,0],[0,0,0],[0,0]],[[-214326,-476280,-83349],[-476280,-333396,-7056],[-83349,-7056]],[[0,0,0],[0,0,0],[0,0]],[[-5286708,-3969000,-230202],[-3969000,-920808,-3087],[-230202,-3087]],[[0,0,0],[0,0,0],[0,0]],[[-47246976,-15705774,-333837],[-15705774,-1335348,-441],[-333837,-441]],[[0,0,0],[0,0],[0]],[[-229455828,-36702666,-280476],[-36702666,-1121904],[-280476]],[[0,0,0],[0,0],[0]],[[-709638678,-55798848,-140679],[-55798848,-562716],[-140679]],[[0,0,0],[0,0],[0]],[[-1516574304,-58004730,-41454],[-58004730,-165816],[-41454]],[[0,0,0],[0,0],[0]],[[-2348967096,-42281757,-6615],[-42281757,-26460],[-6615]],[[0,0,0],[0,0],[0]],[[-2715331374,-21801717,-441],[-21801717,-1764],[-441]],[[0,0],[0]],[[-2385119394,-7906689],[-7906689]],[[0,0],[0]],[[-1607892174,-1971270],[-1971270]],[[0,0],[0]],[[-834724800,-321489],[-321489]],[[0,0],[0]],[[-332775072,-30870],[-30870]],[[0,0],[0]],[[-100887570,-1323],[-1323]],[[0]],[[-22824396]],[[0]],[[-3729096]],[[0]],[[-415422]],[[0]],[[-28224]],[[0]],[[-882]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
