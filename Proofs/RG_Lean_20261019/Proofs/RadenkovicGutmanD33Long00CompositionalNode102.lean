/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode100
import Proofs.RadenkovicGutmanD33Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1089]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-9801],[0,-19602,32274],[-9801,32274,66]],[[0,0,0],[0,0,0],[0,0]],[[-88209,-326997,117315],[-326997,621918,108372],[117315,108372]],[[0,0,0],[0,0,0],[0,0]],[[-4046922,849123,985545],[849123,4370058,118668],[985545,118668]],[[0,0,0],[0,0,0],[0,0]],[[-21429441,23270841,2793186],[23270841,11663058,49896],[2793186,49896]],[[0,0,0],[0,0,0],[0,0]],[[29286576,114717504,4085004],[114717504,16430436,7458],[4085004,7458]],[[0,0,0],[0,0,0],[0,0]],[[653433957,294353037,3458268],[294353037,13527756,132],[3458268,132]],[[0,0,0],[0,0],[0]],[[2947097736,472366587,1753323],[472366587,6711210],[1753323]],[[0,0,0],[0,0],[0]],[[7623894102,510126144,525822],[510126144,1978746],[525822]],[[0,0,0],[0,0],[0]],[[13322487090,383506629,86823],[383506629,322674],[86823]],[[0,0,0],[0,0],[0]],[[16787300904,203280891,6369],[203280891,23562],[6369]],[[0,0,0],[0,0],[0]],[[15765052512,75728862,66],[75728862,264],[66]],[[0,0],[0]],[[11227277490,19430235],[19430235]],[[0,0],[0]],[[6109607262,3281751],[3281751]],[[0,0],[0]],[[2540136093,332277],[332277]],[[0,0],[0]],[[800662368,16104],[16104]],[[0,0],[0]],[[188125146,132],[132]],[[0]],[[31971390]],[[0]],[[3728703]],[[0]],[[270402]],[[0]],[[9735]],[[0]],[[66]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
