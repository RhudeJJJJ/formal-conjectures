/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode100
import Proofs.RadenkovicGutmanD26Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,676]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-6084],[0,-12168,19968],[-6084,19968,52]],[[0,0,0],[0,0,0],[0,0]],[[-54756,-203580,72228],[-203580,384072,67184],[72228,67184]],[[0,0,0],[0,0,0],[0,0]],[[-2520180,506844,608504],[506844,2703064,73840],[608504,73840]],[[0,0,0],[0,0,0],[0,0]],[[-13488228,14303484,1727128],[14303484,7224568,31304],[1727128,31304]],[[0,0,0],[0,0,0],[0,0]],[[16698084,70750784,2529800],[70750784,10195536,4784],[2529800,4784]],[[0,0,0],[0,0,0],[0,0]],[[399375236,181886900,2145936],[181886900,8413808,104],[2145936,104]],[[0,0,0],[0,0],[0]],[[1813178068,292354972,1091116],[292354972,4187976],[1091116]],[[0,0,0],[0,0],[0]],[[4704733592,316232696,328744],[316232696,1241240],[328744]],[[0,0,0],[0,0],[0]],[[8238212944,238160988,54756],[238160988,204360],[54756]],[[0,0,0],[0,0],[0]],[[10398218064,126503988,4108],[126503988,15288],[4108]],[[0,0,0],[0,0],[0]],[[9780153760,47252400,52],[47252400,208],[52]],[[0,0],[0]],[[6975813000,12168260],[12168260]],[[0,0],[0]],[[3802298552,2066740],[2066740]],[[0,0],[0]],[[1583775492,211380],[211380]],[[0,0],[0]],[[500320340,10504],[10504]],[[0,0],[0]],[[117889512,104],[104]],[[0]],[[20113600]],[[0]],[[2359916]],[[0]],[[173004]],[[0]],[[6396]],[[0]],[[52]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
