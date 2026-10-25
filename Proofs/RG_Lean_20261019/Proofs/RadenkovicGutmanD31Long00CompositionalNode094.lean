/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode035
import Proofs.RadenkovicGutmanD31Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-8649],[0,-17298,5394],[-8649,5394]],[[0,0,0],[0,0,0],[0,0]],[[0,-236871,-26412],[-236871,44268,23374],[-26412,23374]],[[0,0,0],[0,0,0],[0,0]],[[-1461402,-1249641,85157],[-1249641,849958,28768],[85157,28768]],[[0,0,0],[0,0,0],[0,0]],[[-10360386,933813,498418],[933813,2873948,12586],[498418,12586]],[[0,0,0],[0,0,0],[0,0]],[[-1920078,22759022,934402],[22759022,4590976,1798],[934402,1798]],[[0,0,0],[0,0],[0]],[[231277608,78792545,903278],[78792545,4093612],[903278]],[[0,0,0],[0,0],[0]],[[1193645328,145872887,495721],[145872887,2138566],[495721]],[[0,0,0],[0,0],[0]],[[3275123836,171492744,155558],[171492744,649140],[155558]],[[0,0,0],[0,0],[0]],[[5919011722,136196547,26009],[136196547,105958],[26009]],[[0,0,0],[0,0],[0]],[[7613033134,74848477,1798],[74848477,7192],[1798]],[[0,0],[0]],[[7237557724,28521116],[28521116]],[[0,0],[0]],[[5187666914,7397995],[7397995]],[[0,0],[0]],[[2828751302,1246355],[1246355]],[[0,0],[0]],[[1174139508,122977],[122977]],[[0,0],[0]],[[368187248,5394],[5394]],[[0]],[[85722936]],[[0]],[[14356286]],[[0]],[[1634134]],[[0]],[[113150]],[[0]],[[3596]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
