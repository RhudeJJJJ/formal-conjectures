/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1444]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-25992,25992],[0,25992]],[[0,0,0],[0,0,0],[0,0]],[[116964,-233928,116964],[-233928,242592,69312],[116964,69312]],[[0,0,0],[0,0,0],[0,0]],[[-77976,-545832,623808],[-545832,1729912,63536],[623808,63536]],[[0,0,0],[0,0,0],[0,0]],[[-4327668,3976776,1403568],[3976776,4291568,23104],[1403568,23104]],[[0,0,0],[0,0,0],[0,0]],[[-11913000,24917664,1732800],[24917664,5648928,2888],[1732800,2888]],[[0,0,0],[0,0],[0]],[[25075060,65930152,1279384],[65930152,4395536],[1279384]],[[0,0,0],[0,0],[0]],[[237919216,105455320,577600],[105455320,2076472],[577600]],[[0,0,0],[0,0],[0]],[[743333656,112764848,155952],[112764848,583376],[155952]],[[0,0,0],[0,0],[0]],[[1429291416,83913728,23104],[83913728,89528],[23104]],[[0,0,0],[0,0],[0]],[[1923673696,44050664,1444],[44050664,5776],[1444]],[[0,0],[0]],[[1907570208,16245000],[16245000]],[[0,0],[0]],[[1427353568,4115400],[4115400]],[[0,0],[0]],[[813910600,681568],[681568]],[[0,0],[0]],[[353833428,66424],[66424]],[[0,0],[0]],[[116334416,2888],[2888]],[[0]],[[28415032]],[[0]],[[4993352]],[[0]],[[596372]],[[0]],[[43320]],[[0]],[[1444]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
