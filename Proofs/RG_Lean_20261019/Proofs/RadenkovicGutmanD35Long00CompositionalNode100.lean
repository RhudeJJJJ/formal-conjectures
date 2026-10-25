/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode043
import Proofs.RadenkovicGutmanD35Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-11025],[0,-22050,6930],[-11025,6930]],[[0,0,0],[0,0,0],[0,0]],[[0,-433755,-33180],[-433755,37590,30030],[-33180,30030]],[[0,0,0],[0,0,0],[0,0]],[[-4025700,-3480435,111965],[-3480435,916930,36960],[111965,36960]],[[0,0,0],[0,0,0],[0,0]],[[-48346200,-10337355,644770],[-10337355,3089030,16170],[644770,16170]],[[0,0,0],[0,0,0],[0,0]],[[-256607190,-10673460,1204770],[-10673460,4848900,2310],[1204770,2310]],[[0,0,0],[0,0],[0]],[[-792799350,14400785,1162910],[14400785,4238500],[1162910]],[[0,0,0],[0,0],[0]],[[-1568140910,61343345,637665],[61343345,2171610],[637665]],[[0,0,0],[0,0],[0]],[[-2024750840,93881200,199990],[93881200,647150],[199990]],[[0,0,0],[0,0],[0]],[[-1579280430,85720635,33425],[85720635,103810],[33425]],[[0,0,0],[0,0],[0]],[[-384965140,51546145,2310],[51546145,6930],[2310]],[[0,0],[0]],[[716484440,20956530],[20956530]],[[0,0],[0]],[[1093230950,5714275],[5714275]],[[0,0],[0]],[[845355910,1002365],[1002365]],[[0,0],[0]],[[435691410,102305],[102305]],[[0,0],[0]],[[159063450,4620],[4620]],[[0]],[[41540100]],[[0]],[[7619150]],[[0]],[[934360]],[[0]],[[68880]],[[0]],[[2310]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
