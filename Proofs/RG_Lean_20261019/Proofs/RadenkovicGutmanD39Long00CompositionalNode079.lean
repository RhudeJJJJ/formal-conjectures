/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode033
import Proofs.RadenkovicGutmanD39Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4563],[0,4563]],[[0,0,0],[0,0,0],[0,0]],[[0,-41067,41067],[-41067,150579,19773],[41067,19773]],[[0,0,0],[0,0,0],[0,0]],[[-616005,451737,287469],[451737,1031238,24336],[287469,24336]],[[0,0,0],[0,0,0],[0,0]],[[-3901365,6351696,793962],[6351696,2772783,10647],[793962,10647]],[[0,0,0],[0,0,0],[0,0]],[[2135484,28745379,1151397],[28745379,3908970,1521],[1151397,1521]],[[0,0,0],[0,0],[0]],[[100481823,71173674,967356],[71173674,3194100],[967356]],[[0,0,0],[0,0],[0]],[[477638109,111810231,485199],[111810231,1560546],[485199]],[[0,0,0],[0,0],[0]],[[1264209570,118963494,142974],[118963494,448695],[142974]],[[0,0,0],[0,0],[0]],[[2243992140,88414209,22815],[88414209,69966],[22815]],[[0,0,0],[0,0],[0]],[[2865982275,46401147,1521],[46401147,4563],[1521]],[[0,0],[0]],[[2726088300,17111250],[17111250]],[[0,0],[0]],[[1965503124,4334850],[4334850]],[[0,0],[0]],[[1082088072,717912],[717912]],[[0,0],[0]],[[454604085,69966],[69966]],[[0,0],[0]],[[144514773,3042],[3042]],[[0]],[[34140366]],[[0]],[[5804136]],[[0]],[[670761]],[[0]],[[47151]],[[0]],[[1521]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
