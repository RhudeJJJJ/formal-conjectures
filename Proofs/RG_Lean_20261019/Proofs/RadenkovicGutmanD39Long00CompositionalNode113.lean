/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1521]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-27378,27378],[0,27378]],[[0,0,0],[0,0,0],[0,0]],[[123201,-246402,123201],[-246402,255528,73008],[123201,73008]],[[0,0,0],[0,0,0],[0,0]],[[-82134,-574938,657072],[-574938,1822158,66924],[657072,66924]],[[0,0,0],[0,0,0],[0,0]],[[-4558437,4188834,1478412],[4188834,4520412,24336],[1478412,24336]],[[0,0,0],[0,0,0],[0,0]],[[-12548250,26246376,1825200],[26246376,5950152,3042],[1825200,3042]],[[0,0,0],[0,0],[0]],[[26412165,69445818,1347606],[69445818,4629924],[1347606]],[[0,0,0],[0,0],[0]],[[250606044,111078630,608400],[111078630,2187198],[608400]],[[0,0,0],[0,0],[0]],[[782971254,118777932,164268],[118777932,614484],[164268]],[[0,0,0],[0,0],[0]],[[1505507094,88388352,24336],[88388352,94302],[24336]],[[0,0,0],[0,0],[0]],[[2026251864,46399626,1521],[46399626,6084],[1521]],[[0,0],[0]],[[2009289672,17111250],[17111250]],[[0,0],[0]],[[1503465912,4334850],[4334850]],[[0,0],[0]],[[857311650,717912],[717912]],[[0,0],[0]],[[372701277,69966],[69966]],[[0,0],[0]],[[122537844,3042],[3042]],[[0]],[[29930238]],[[0]],[[5259618]],[[0]],[[628173]],[[0]],[[45630]],[[0]],[[1521]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
