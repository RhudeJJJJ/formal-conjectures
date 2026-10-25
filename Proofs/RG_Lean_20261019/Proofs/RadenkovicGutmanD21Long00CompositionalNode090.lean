/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode035
import Proofs.RadenkovicGutmanD21Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1323],[0,-1323]],[[0,0,0],[0,0,0],[0,0]],[[0,-11907,-19845],[-11907,-63504,-5859],[-19845,-5859]],[[0,0,0],[0,0,0],[0,0]],[[-214326,-739368,-153279],[-739368,-475524,-7602],[-153279,-7602]],[[0,0,0],[0,0,0],[0,0]],[[-7450380,-6943482,-471870],[-6943482,-1420020,-3759],[-471870,-3759]],[[0,0,0],[0,0,0],[0,0]],[[-77041692,-30078468,-759717],[-30078468,-2230956,-735],[-759717,-735]],[[0,0,0],[0,0,0],[0,0]],[[-412512912,-76080354,-703878],[-76080354,-2032296,-42],[-703878,-42]],[[0,0,0],[0,0],[0]],[[-1377835326,-124318026,-387891],[-124318026,-1110564],[-387891]],[[0,0,0],[0,0],[0]],[[-3144060612,-138233340,-126294],[-138233340,-362292],[-126294]],[[0,0,0],[0,0],[0]],[[-5162437056,-107460969,-22911],[-107460969,-66948],[-22911]],[[0,0,0],[0,0],[0]],[[-6296292618,-59043789,-1953],[-59043789,-6048],[-1953]],[[0,0,0],[0,0],[0]],[[-5817121338,-22868181,-42],[-22868181,-168],[-42]],[[0,0],[0]],[[-4117422498,-6134100],[-6134100]],[[0,0],[0]],[[-2243276784,-1095759],[-1095759]],[[0,0],[0]],[[-939548148,-120582],[-120582]],[[0,0],[0]],[[-300185130,-6909],[-6909]],[[0,0],[0]],[[-72027480,-126],[-126]],[[0]],[[-12634272]],[[0]],[[-1548498]],[[0]],[[-122472]],[[0]],[[-5334]],[[0]],[[-84]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
