/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode035
import Proofs.RadenkovicGutmanD21Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-3969],[0,-7938,2394],[-3969,2394]],[[0,0,0],[0,0,0],[0,0]],[[0,-109431,-12852],[-109431,17388,10374],[-12852,10374]],[[0,0,0],[0,0,0],[0,0]],[[-683802,-602721,33957],[-602721,369558,12768],[33957,12768]],[[0,0,0],[0,0,0],[0,0]],[[-5079186,184653,214578],[184653,1262268,5586],[214578,5586]],[[0,0,0],[0,0,0],[0,0]],[[-3784158,9479022,408282],[9479022,2024736,798],[408282,798]],[[0,0,0],[0,0],[0]],[[92033928,33902505,397278],[33902505,1809612],[397278]],[[0,0,0],[0,0],[0]],[[504157248,63512127,218841],[63512127,946806],[218841]],[[0,0,0],[0,0],[0]],[[1409760156,75133464,68838],[75133464,287700],[68838]],[[0,0,0],[0,0],[0]],[[2571886842,59902227,11529],[59902227,46998],[11529]],[[0,0,0],[0,0],[0]],[[3326757294,33008157,798],[33008157,3192],[798]],[[0,0],[0]],[[3174742284,12602436],[12602436]],[[0,0],[0]],[[2281809474,3273795],[3273795]],[[0,0],[0]],[[1246816662,552195],[552195]],[[0,0],[0]],[[518362068,54537],[54537]],[[0,0],[0]],[[162761088,2394],[2394]],[[0]],[[37935576]],[[0]],[[6358926]],[[0]],[[724374]],[[0]],[[50190]],[[0]],[[1596]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
