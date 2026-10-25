/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode051
import Proofs.RadenkovicGutmanD8Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e051 e061
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,192],[0,192,-96]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-1728,2880],[-1728,8640,-1424],[2880,-1424,-24]],[[0,0,0],[0,0,0],[0,0]],[[-18144,52272,9552],[52272,12672,-6304],[9552,-6304]],[[0,0,0],[0,0,0],[0,0]],[[192888,357120,-9352],[357120,-127200,-7744],[-9352,-7744]],[[0,0,0],[0,0,0],[0,0]],[[2540160,443024,-88480],[443024,-517440,-3760],[-88480,-3760]],[[0,0,0],[0,0,0],[0,0]],[[8081976,-2353120,-174224],[-2353120,-868288,-752],[-174224,-752]],[[0,0,0],[0,0,0],[0,0]],[[-4093664,-10796672,-173376],[-10796672,-801920,-48],[-173376,-48]],[[0,0,0],[0,0],[0]],[[-102025352,-21735040,-99424],[-21735040,-439616],[-99424]],[[0,0,0],[0,0],[0]],[[-356320128,-26763120,-33760],[-26763120,-144704],[-33760]],[[0,0,0],[0,0],[0]],[[-717792592,-22065584,-6576],[-22065584,-27520],[-6576]],[[0,0,0],[0,0],[0]],[[-986838592,-12608816,-656],[-12608816,-2688],[-656]],[[0,0,0],[0,0],[0]],[[-985508544,-5038512,-24],[-5038512,-96],[-24]],[[0,0],[0]],[[-736398208,-1394032],[-1394032]],[[0,0],[0]],[[-417580480,-258800],[-258800]],[[0,0],[0]],[[-180460256,-30208],[-30208]],[[0,0],[0]],[[-59197128,-1936],[-1936]],[[0,0],[0]],[[-14553984,-48],[-48]],[[0]],[[-2618320]],[[0]],[[-330784]],[[0]],[[-27304]],[[0]],[[-1280]],[[0]],[[-24]]]
theorem step072 : p072=NestedArithmetic.mul p051 p061 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e051 e061 p051 p061 p072 rfl h051 h061 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
