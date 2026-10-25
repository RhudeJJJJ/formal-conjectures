/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode089
import Proofs.RadenkovicGutmanD37Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,8214],[0,8214,-2590]],[[0,0,0],[0,0,0],[0,0]],[[0,0,98568],[0,332667,-10804],[98568,-10804]],[[0,0,0],[0,0,0],[0,0]],[[320679,2700297,523254],[2700297,1559106,-79550],[523254,-79550]],[[0,0,0],[0,0,0],[0,0]],[[23225751,23434542,1049912],[23434542,2385723,-93610],[1049912,-93610]],[[0,0,0],[0,0,0],[0,0]],[[251526222,88528383,847818],[88528383,256262,-38184],[847818,-38184]],[[0,0,0],[0,0,0],[0,0]],[[1312131111,189978276,-94942],[189978276,-3418948,-5106],[-94942,-5106]],[[0,0,0],[0,0],[0]],[[4174240433,252495289,-689754],[252495289,-4470266],[-689754]],[[0,0,0],[0,0],[0]],[[8948426246,209480014,-533244],[209480014,-2687421],[-533244]],[[0,0,0],[0,0],[0]],[[13605149528,97689842,-193362],[97689842,-869278],[-193362]],[[0,0,0],[0,0],[0]],[[15062374733,9154096,-34854],[9154096,-146261],[-34854]],[[0,0,0],[0,0],[0]],[[12254238606,-19084489,-2516],[-19084489,-10064],[-2516]],[[0,0],[0]],[[7262916702,-13575966],[-13575966]],[[0,0],[0]],[[3015423928,-4699481],[-4699481]],[[0,0],[0]],[[768652097,-940244],[-940244]],[[0,0],[0]],[[42263509,-104081],[-104081]],[[0,0],[0]],[[-54828746,-4958],[-4958]],[[0]],[[-25497292]],[[0]],[[-6016533]],[[0]],[[-850371]],[[0]],[[-68561]],[[0]],[[-2442]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
