/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode035
import Proofs.RadenkovicGutmanD24Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1728],[0,-1728]],[[0,0,0],[0,0,0],[0,0]],[[0,-15552,-15552],[-15552,-62208,-7488],[-15552,-7488]],[[0,0,0],[0,0,0],[0,0]],[[-279936,-622080,-108864],[-622080,-435456,-9216],[-108864,-9216]],[[0,0,0],[0,0,0],[0,0]],[[-6905088,-5184000,-300672],[-5184000,-1202688,-4032],[-300672,-4032]],[[0,0,0],[0,0,0],[0,0]],[[-61710336,-20513664,-436032],[-20513664,-1744128,-576],[-436032,-576]],[[0,0,0],[0,0],[0]],[[-299697408,-47938176,-366336],[-47938176,-1465344],[-366336]],[[0,0,0],[0,0],[0]],[[-926875008,-72880128,-183744],[-72880128,-734976],[-183744]],[[0,0,0],[0,0],[0]],[[-1980831744,-75761280,-54144],[-75761280,-216576],[-54144]],[[0,0,0],[0,0],[0]],[[-3068038656,-55225152,-8640],[-55225152,-34560],[-8640]],[[0,0,0],[0,0],[0]],[[-3546555264,-28475712,-576],[-28475712,-2304],[-576]],[[0,0],[0]],[[-3115257984,-10327104],[-10327104]],[[0,0],[0]],[[-2100104064,-2574720],[-2574720]],[[0,0],[0]],[[-1090252800,-419904],[-419904]],[[0,0],[0]],[[-434644992,-40320],[-40320]],[[0,0],[0]],[[-131771520,-1728],[-1728]],[[0]],[[-29811456]],[[0]],[[-4870656]],[[0]],[[-542592]],[[0]],[[-36864]],[[0]],[[-1152]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
