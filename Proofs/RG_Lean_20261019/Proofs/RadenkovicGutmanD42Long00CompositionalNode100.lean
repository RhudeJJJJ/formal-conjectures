/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode043
import Proofs.RadenkovicGutmanD42Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-15876],[0,-31752,10080],[-15876,10080]],[[0,0,0],[0,0,0],[0,0]],[[0,-623700,-46872],[-623700,57456,43680],[-46872,43680]],[[0,0,0],[0,0,0],[0,0]],[[-5783400,-4978260,167580],[-4978260,1343160,53760],[167580,53760]],[[0,0,0],[0,0,0],[0,0]],[[-69287400,-14614236,946008],[-14614236,4509456,23520],[946008,23520]],[[0,0,0],[0,0,0],[0,0]],[[-366622200,-14322840,1760304],[-14322840,7068768,3360],[1760304,3360]],[[0,0,0],[0,0],[0]],[[-1127962080,23121252,1695960],[23121252,6174000],[1695960]],[[0,0,0],[0,0],[0]],[[-2217087264,91865004,928956],[91865004,3161592],[928956]],[[0,0,0],[0,0],[0]],[[-2830651152,138762288,291144],[138762288,941808],[291144]],[[0,0,0],[0,0],[0]],[[-2146719960,125972868,48636],[125972868,151032],[48636]],[[0,0,0],[0,0],[0]],[[-411804120,75498444,3360],[75498444,10080],[3360]],[[0,0],[0]],[[1152861696,30626232],[30626232]],[[0,0],[0]],[[1653243480,8337420],[8337420]],[[0,0],[0]],[[1256990616,1460676],[1460676]],[[0,0],[0]],[[642705840,148932],[148932]],[[0,0],[0]],[[233545536,6720],[6720]],[[0]],[[60802560]],[[0]],[[11127480]],[[0]],[[1362312]],[[0]],[[100296]],[[0]],[[3360]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
