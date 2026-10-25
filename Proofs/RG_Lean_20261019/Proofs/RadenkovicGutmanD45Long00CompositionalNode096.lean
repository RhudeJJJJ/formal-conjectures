/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode043
import Proofs.RadenkovicGutmanD45Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,6075],[0,6075,-3870]],[[0,0,0],[0,0,0],[0,0]],[[0,54675,54675],[54675,221940,-43335],[54675,-43335]],[[0,0,0],[0,0,0],[0,0]],[[1326780,2216160,69255],[2216160,305100,-153360],[69255,-153360]],[[0,0,0],[0,0,0],[0,0]],[[30477060,12913020,-614790],[12913020,-2363760,-156105],[-614790,-156105]],[[0,0,0],[0,0,0],[0,0]],[[241145910,28582470,-2228715],[28582470,-8749980,-59895],[-2228715,-59895]],[[0,0,0],[0,0,0],[0,0]],[[1015533180,11199330,-3356100],[11199330,-13264560,-7740],[-3356100,-7740]],[[0,0,0],[0,0],[0]],[[2645757180,-78785640,-2782845],[-78785640,-11041380],[-2782845]],[[0,0,0],[0,0],[0]],[[4513759200,-202106250,-1357650],[-202106250,-5401440],[-1357650]],[[0,0,0],[0,0],[0]],[[4992976260,-258808995,-387585],[-258808995,-1545300],[-387585]],[[0,0,0],[0,0],[0]],[[3053063790,-210243915,-59895],[-210243915,-239220],[-59895]],[[0,0,0],[0,0],[0]],[[-218443590,-115485975,-3870],[-115485975,-15480],[-3870]],[[0,0],[0]],[[-2584618650,-43563150],[-43563150]],[[0,0],[0]],[[-2958652800,-11139975],[-11139975]],[[0,0],[0]],[[-2025820440,-1847250],[-1847250]],[[0,0],[0]],[[-962574120,-179325],[-179325]],[[0,0],[0]],[[-329779620,-7740],[-7740]],[[0]],[[-81650700]],[[0]],[[-14296050]],[[0]],[[-1682010]],[[0]],[[-119430]],[[0]],[[-3870]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
