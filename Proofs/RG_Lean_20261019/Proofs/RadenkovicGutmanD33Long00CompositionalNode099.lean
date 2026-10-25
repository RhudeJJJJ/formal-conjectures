/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode096
import Proofs.RadenkovicGutmanD33Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,6534],[0,6534,-2046]],[[0,0,0],[0,0,0],[0,0]],[[0,0,78408],[0,267003,-8316],[78408,-8316]],[[0,0,0],[0,0,0],[0,0]],[[275319,2169585,417582],[2169585,1265616,-62502],[417582,-62502]],[[0,0,0],[0,0,0],[0,0]],[[19016613,18907020,842688],[18907020,1992639,-73722],[842688,-73722]],[[0,0,0],[0,0,0],[0,0]],[[205525188,71767971,692010],[71767971,377652,-30096],[692010,-30096]],[[0,0,0],[0,0,0],[0,0]],[[1073390175,154918038,-52998],[154918038,-2542584,-4026],[-52998,-4026]],[[0,0,0],[0,0],[0]],[[3421878999,207563565,-531498],[207563565,-3450546],[-531498]],[[0,0,0],[0,0],[0]],[[7354441776,174530664,-416196],[174530664,-2100945],[-416196]],[[0,0,0],[0,0],[0]],[[11215252620,84075882,-151602],[84075882,-684288],[-151602]],[[0,0,0],[0,0],[0]],[[12461242101,10834692,-27390],[10834692,-115665],[-27390]],[[0,0,0],[0,0],[0]],[[10185171744,-13820169,-1980],[-13820169,-7986],[-1980]],[[0,0],[0]],[[6077375634,-10452684],[-10452684]],[[0,0],[0]],[[2553152316,-3684021],[-3684021]],[[0,0],[0]],[[670379457,-743754],[-743754]],[[0,0],[0]],[[49741791,-82797],[-82797]],[[0,0],[0]],[[-40695336,-3960],[-3960]],[[0]],[[-20017800]],[[0]],[[-4800741]],[[0]],[[-683925]],[[0]],[[-55407]],[[0]],[[-1980]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
