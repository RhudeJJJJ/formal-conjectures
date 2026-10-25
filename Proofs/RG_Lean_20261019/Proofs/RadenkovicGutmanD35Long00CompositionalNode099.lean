/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode096
import Proofs.RadenkovicGutmanD35Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,7350],[0,7350,-2310]],[[0,0,0],[0,0,0],[0,0]],[[0,0,88200],[0,300195,-9520],[88200,-9520]],[[0,0,0],[0,0,0],[0,0]],[[309015,2439045,468930],[2439045,1419180,-70770],[468930,-70770]],[[0,0,0],[0,0,0],[0,0]],[[21365505,21236040,943460],[21236040,2219455,-83370],[943460,-83370]],[[0,0,0],[0,0,0],[0,0]],[[230829480,80521875,767970],[80521875,376320,-34020],[767970,-34020]],[[0,0,0],[0,0,0],[0,0]],[[1204976535,173569970,-73010],[173569970,-2919280,-4550],[-73010,-4550]],[[0,0,0],[0,0],[0]],[[3839263715,232068725,-608090],[232068725,-3924690],[-608090]],[[0,0,0],[0,0],[0]],[[8246198380,194406940,-472920],[194406940,-2382625],[-472920]],[[0,0,0],[0,0],[0]],[[12565206500,92768690,-171850],[92768690,-774900],[-171850]],[[0,0,0],[0,0],[0]],[[13946728285,10981600,-31010],[10981600,-130865],[-31010]],[[0,0,0],[0,0],[0]],[[11382630700,-16120685,-2240],[-16120685,-9030],[-2240]],[[0,0],[0]],[[6776202930,-11951940],[-11951940]],[[0,0],[0]],[[2834496700,-4189325],[-4189325]],[[0,0],[0]],[[735989625,-843570],[-843570]],[[0,0],[0]],[[49207235,-93765],[-93765]],[[0,0],[0]],[[-47696460,-4480],[-4480]],[[0]],[[-22926400]],[[0]],[[-5463325]],[[0]],[[-775985]],[[0]],[[-62755]],[[0]],[[-2240]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
