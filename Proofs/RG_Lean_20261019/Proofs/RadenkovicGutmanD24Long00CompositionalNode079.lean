/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode033
import Proofs.RadenkovicGutmanD24Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1728],[0,1728]],[[0,0,0],[0,0,0],[0,0]],[[0,-15552,15552],[-15552,57024,7488],[15552,7488]],[[0,0,0],[0,0,0],[0,0]],[[-233280,171072,108864],[171072,390528,9216],[108864,9216]],[[0,0,0],[0,0,0],[0,0]],[[-1477440,2405376,300672],[2405376,1050048,4032],[300672,4032]],[[0,0,0],[0,0,0],[0,0]],[[808704,10885824,436032],[10885824,1480320,576],[436032,576]],[[0,0,0],[0,0],[0]],[[38052288,26953344,366336],[26953344,1209600],[366336]],[[0,0,0],[0,0],[0]],[[180880704,42342336,183744],[42342336,590976],[183744]],[[0,0,0],[0,0],[0]],[[478753920,45051264,54144],[45051264,169920],[54144]],[[0,0,0],[0,0],[0]],[[849795840,33482304,8640],[33482304,26496],[8640]],[[0,0,0],[0,0],[0]],[[1085342400,17572032,576],[17572032,1728],[576]],[[0,0],[0]],[[1032364800,6480000],[6480000]],[[0,0],[0]],[[744332544,1641600],[1641600]],[[0,0],[0]],[[409784832,271872],[271872]],[[0,0],[0]],[[172157760,26496],[26496]],[[0,0],[0]],[[54727488,1152],[1152]],[[0]],[[12928896]],[[0]],[[2198016]],[[0]],[[254016]],[[0]],[[17856]],[[0]],[[576]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
