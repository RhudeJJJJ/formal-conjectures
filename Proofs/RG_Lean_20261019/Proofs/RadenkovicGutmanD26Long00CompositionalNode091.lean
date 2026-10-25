/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2028],[0,2028]],[[0,0,0],[0,0,0],[0,0]],[[0,18252,30420],[18252,97344,8944],[30420,8944]],[[0,0,0],[0,0,0],[0,0]],[[328536,1133028,234624],[1133028,727584,11492],[234624,11492]],[[0,0,0],[0,0,0],[0,0]],[[11414520,10630152,720980],[10630152,2167360,5564],[720980,5564]],[[0,0,0],[0,0,0],[0,0]],[[117947232,45995248,1158092],[45995248,3393936,1040],[1158092,1040]],[[0,0,0],[0,0,0],[0,0]],[[631006272,116181104,1069588],[116181104,3077776,52],[1069588,52]],[[0,0,0],[0,0],[0]],[[2105614056,189534176,586716],[189534176,1670864],[586716]],[[0,0,0],[0,0],[0]],[[4799544152,210328560,189644],[210328560,539552],[189644]],[[0,0,0],[0,0],[0]],[[7870818176,163096284,33956],[163096284,97968],[33956]],[[0,0,0],[0,0],[0]],[[9585513288,89319984,2808],[89319984,8528],[2808]],[[0,0,0],[0,0],[0]],[[8840715728,34442096,52],[34442096,208],[52]],[[0,0],[0]],[[6244552288,9180860],[9180860]],[[0,0],[0]],[[3393532584,1624324],[1624324]],[[0,0],[0]],[[1416779728,175812],[175812]],[[0,0],[0]],[[450805160,9724],[9724]],[[0,0],[0]],[[107577080,156],[156]],[[0]],[[18726032]],[[0]],[[2268968]],[[0]],[[176072]],[[0]],[[7384]],[[0]],[[104]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
