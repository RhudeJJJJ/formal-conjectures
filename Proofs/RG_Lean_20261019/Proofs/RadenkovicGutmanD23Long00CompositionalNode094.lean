/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode035
import Proofs.RadenkovicGutmanD23Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-4761],[0,-9522,2898],[-4761,2898]],[[0,0,0],[0,0,0],[0,0]],[[0,-131031,-15180],[-131031,21804,12558],[-15180,12558]],[[0,0,0],[0,0,0],[0,0]],[[-815994,-713529,42389],[-713529,449926,15456],[42389,15456]],[[0,0,0],[0,0,0],[0,0]],[[-5987682,300357,261970],[300357,1532444,6762],[261970,6762]],[[0,0,0],[0,0,0],[0,0]],[[-3600558,11682574,496386],[11682574,2455296,966],[496386,966]],[[0,0,0],[0,0],[0]],[[114957864,41396849,482126],[41396849,2193004],[482126]],[[0,0,0],[0,0],[0]],[[618859344,77294375,265305],[77294375,1146918],[265305]],[[0,0,0],[0,0],[0]],[[1721204540,91278536,83398],[91278536,348404],[83398]],[[0,0,0],[0,0],[0]],[[3131767722,72695571,13961],[72695571,56902],[13961]],[[0,0,0],[0,0],[0]],[[4044548942,40027981,966],[40027981,3864],[966]],[[0,0],[0]],[[3855639132,15274300],[15274300]],[[0,0],[0]],[[2769082562,3966235],[3966235]],[[0,0],[0]],[[1512199078,668771],[668771]],[[0,0],[0]],[[628411060,66033],[66033]],[[0,0],[0]],[[197243952,2898],[2898]],[[0]],[[45958968]],[[0]],[[7701918]],[[0]],[[877174]],[[0]],[[60766]],[[0]],[[1932]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
