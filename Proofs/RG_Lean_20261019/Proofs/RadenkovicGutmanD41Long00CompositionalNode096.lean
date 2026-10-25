/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode043
import Proofs.RadenkovicGutmanD41Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5043],[0,5043,-3198]],[[0,0,0],[0,0,0],[0,0]],[[0,45387,45387],[45387,184500,-35711],[45387,-35711]],[[0,0,0],[0,0,0],[0,0]],[[1102572,1842048,58671],[1842048,260268,-126608],[58671,-126608]],[[0,0,0],[0,0,0],[0,0]],[[25341444,10767420,-504054],[10767420,-1929296,-128945],[-504054,-128945]],[[0,0,0],[0,0,0],[0,0]],[[200732310,24026902,-1835939],[24026902,-7193532,-49487],[-1835939,-49487]],[[0,0,0],[0,0,0],[0,0]],[[846624252,10263858,-2768484],[10263858,-10928304,-6396],[-2768484,-6396]],[[0,0,0],[0,0],[0]],[[2210447596,-63485384,-2297189],[-63485384,-9106756],[-2297189]],[[0,0,0],[0,0],[0]],[[3783956256,-165240250,-1121186],[-165240250,-4458176],[-1121186]],[[0,0,0],[0,0],[0]],[[4213397636,-212513947,-320169],[-212513947,-1276084],[-320169]],[[0,0,0],[0,0],[0]],[[2628309182,-173006019,-49487],[-173006019,-197620],[-49487]],[[0,0,0],[0,0],[0]],[[-84228022,-95156367,-3198],[-95156367,-12792],[-3198]],[[0,0],[0]],[[-2068489770,-35927070],[-35927070]],[[0,0],[0]],[[-2408742784,-9193471],[-9193471]],[[0,0],[0]],[[-1659173240,-1525282],[-1525282]],[[0,0],[0]],[[-790785368,-148133],[-148133]],[[0,0],[0]],[[-271435908,-6396],[-6396]],[[0]],[[-67291660]],[[0]],[[-11792994]],[[0]],[[-1388506]],[[0]],[[-98646]],[[0]],[[-3198]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
