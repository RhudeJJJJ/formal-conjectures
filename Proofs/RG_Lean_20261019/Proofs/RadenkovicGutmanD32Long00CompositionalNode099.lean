/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode096
import Proofs.RadenkovicGutmanD32Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,6144],[0,6144,-1920]],[[0,0,0],[0,0,0],[0,0]],[[0,0,73728],[0,251136,-7744],[73728,-7744]],[[0,0,0],[0,0,0],[0,0]],[[259200,2040768,393024],[2040768,1192128,-58560],[393024,-58560]],[[0,0,0],[0,0,0],[0,0]],[[17893440,17793216,794432],[17793216,1883776,-69120],[794432,-69120]],[[0,0,0],[0,0,0],[0,0]],[[193423680,67579776,655488],[67579776,377280,-28224],[655488,-28224]],[[0,0,0],[0,0,0],[0,0]],[[1010448384,145989056,-43712],[145989056,-2363776,-3776],[-43712,-3776]],[[0,0,0],[0,0],[0]],[[3222186560,195822080,-495104],[195822080,-3224832],[-495104]],[[0,0,0],[0,0],[0]],[[6927679168,164991040,-389184],[164991040,-1966720],[-389184]],[[0,0,0],[0,0],[0]],[[10569000320,79883648,-141952],[79883648,-641088],[-141952]],[[0,0,0],[0,0],[0]],[[11749795840,10739392,-25664],[10739392,-108416],[-25664]],[[0,0,0],[0,0],[0]],[[9611306944,-12732608,-1856],[-12732608,-7488],[-1856]],[[0,0],[0]],[[5742126336,-9740160],[-9740160]],[[0,0],[0]],[[2417906176,-3443456],[-3443456]],[[0,0],[0]],[[638644992,-696192],[-696192]],[[0,0],[0]],[[49856960,-77568],[-77568]],[[0,0],[0]],[[-37389120,-3712],[-3712]],[[0]],[[-18636160]],[[0]],[[-4485376]],[[0]],[[-640064]],[[0]],[[-51904]],[[0]],[[-1856]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
