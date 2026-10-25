/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode033
import Proofs.RadenkovicGutmanD21Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,441]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,10584],[0,10584,42]],[[0,0,0],[0,0,0],[0,0]],[[-35721,-23814,59535],[-23814,230202,33390],[59535,33390]],[[0,0,0],[0,0,0],[0,0]],[[-979776,904932,360612],[904932,1373652,35532],[360612,35532]],[[0,0,0],[0,0,0],[0,0]],[[-4214511,8888292,907200],[8888292,3395070,15078],[907200,15078]],[[0,0,0],[0,0,0],[0,0]],[[10054422,35590842,1237698],[35590842,4546836,2436],[1237698,2436]],[[0,0,0],[0,0,0],[0,0]],[[144864909,82082700,1002078],[82082700,3616704,84],[1002078,84]],[[0,0,0],[0,0],[0]],[[601646808,122971212,494970],[122971212,1759380],[494970]],[[0,0,0],[0,0],[0]],[[1486287642,126621432,147336],[126621432,517902],[147336]],[[0,0,0],[0,0],[0]],[[2521568280,92106378,24822],[92106378,86940],[24822]],[[0,0,0],[0,0],[0]],[[3118500546,47805366,1995],[47805366,7098],[1995]],[[0,0,0],[0,0],[0]],[[2898079716,17633826,42],[17633826,168],[42]],[[0,0],[0]],[[2056124784,4536000],[4536000]],[[0,0],[0]],[[1121210328,781620],[781620]],[[0,0],[0]],[[469730121,83412],[83412]],[[0,0],[0]],[[150090192,4662],[4662]],[[0,0],[0]],[[36013698,84],[84]],[[0]],[[6317136]],[[0]],[[774249]],[[0]],[[61236]],[[0]],[[2667]],[[0]],[[42]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
