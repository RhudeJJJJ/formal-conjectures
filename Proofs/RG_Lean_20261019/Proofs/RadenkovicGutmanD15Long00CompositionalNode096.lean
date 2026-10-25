/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode043
import Proofs.RadenkovicGutmanD15Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,675],[0,675,-390]],[[0,0,0],[0,0,0],[0,0]],[[0,6075,6075],[6075,25380,-4095],[6075,-4095]],[[0,0,0],[0,0,0],[0,0]],[[150660,252720,10935],[252720,53100,-15120],[10935,-15120]],[[0,0,0],[0,0,0],[0,0]],[[3500820,1566540,-51030],[1566540,-172320,-15585],[-51030,-15585]],[[0,0,0],[0,0,0],[0,0]],[[28307070,3998790,-208755],[3998790,-780060,-6015],[-208755,-6015]],[[0,0,0],[0,0,0],[0,0]],[[122732460,3897810,-324900],[3897810,-1246320,-780],[-324900,-780]],[[0,0,0],[0,0],[0]],[[332778660,-3495480,-273765],[-3495480,-1065060],[-273765]],[[0,0,0],[0,0],[0]],[[602995200,-15506250,-134850],[-15506250,-529680],[-134850]],[[0,0,0],[0,0],[0]],[[743036820,-22364715,-38745],[-22364715,-153300],[-38745]],[[0,0,0],[0,0],[0]],[[596852430,-19183155,-6015],[-19183155,-23940],[-6015]],[[0,0,0],[0,0],[0]],[[242180970,-10880175,-390],[-10880175,-1560],[-390]],[[0,0],[0]],[[-75727050,-4193550],[-4193550]],[[0,0],[0]],[[-198940800,-1089375],[-1089375]],[[0,0],[0]],[[-163331880,-182850],[-182850]],[[0,0],[0]],[[-84260640,-17925],[-17925]],[[0,0],[0]],[[-30271140,-780],[-780]],[[0]],[[-7731900]],[[0]],[[-1384050]],[[0]],[[-165570]],[[0]],[[-11910]],[[0]],[[-390]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
