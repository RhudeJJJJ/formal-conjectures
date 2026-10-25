/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode033
import Proofs.RadenkovicGutmanD13Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,169]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,4056],[0,4056,26]],[[0,0,0],[0,0,0],[0,0]],[[-13689,-9126,22815],[-9126,88218,12974],[22815,12974]],[[0,0,0],[0,0,0],[0,0]],[[-376272,346788,138996],[346788,529620,14092],[138996,14092]],[[0,0,0],[0,0,0],[0,0]],[[-1628991,3420612,351936],[3420612,1318174,6214],[351936,6214]],[[0,0,0],[0,0,0],[0,0]],[[3810534,13754650,483938],[13754650,1780948,1092],[483938,1092]],[[0,0,0],[0,0,0],[0,0]],[[55717181,31869708,395902],[31869708,1433536,52],[395902,52]],[[0,0,0],[0,0],[0]],[[232488776,48002188,198458],[48002188,709332],[198458]],[[0,0,0],[0,0],[0]],[[576683770,49746008,60424],[49746008,214318],[60424]],[[0,0,0],[0,0],[0]],[[982554872,36475114,10582],[36475114,37596],[10582]],[[0,0,0],[0,0],[0]],[[1220933090,19124950,923],[19124950,3354],[923]],[[0,0,0],[0,0],[0]],[[1140853220,7150338,26],[7150338,104],[26]],[[0,0],[0]],[[814652592,1874080],[1874080]],[[0,0],[0]],[[447708248,332020],[332020]],[[0,0],[0]],[[189381049,37076],[37076]],[[0,0],[0]],[[61254336,2262],[2262]],[[0,0],[0]],[[14934114,52],[52]],[[0]],[[2677168]],[[0]],[[338585]],[[0]],[[28132]],[[0]],[[1339]],[[0]],[[26]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
