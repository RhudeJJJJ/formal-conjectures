/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode289
import Proofs.RadenkovicGutmanD40Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[6400,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[192000,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2643200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[22131200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[125939200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[515622400,6400,0],[6400,0],[0]],[[0,0,0],[0,0],[0]],[[1568531200,140800,0],[140800,0],[0]],[[0,0,0],[0,0],[0]],[[3610380800,1376000,0],[1376000,0],[0]],[[0,0,0],[0,0],[0]],[[6344460800,7872000,0],[7872000,0],[0]],[[0,0,0],[0,0],[0]],[[8526604800,29254400,0],[29254400,0],[0]],[[0,0,0],[0,0],[0]],[[8721222400,74112000,1600],[74112000,3200],[1600]],[[0,0,0],[0,0],[0]],[[6706828800,130726400,22400],[130726400,44800],[22400]],[[0,0,0],[0,0],[0]],[[3795033600,161152000,129600],[161152000,259200],[129600]],[[0,0,0],[0,0],[0]],[[1524441600,137286400,400000],[137286400,800000],[400000]],[[0,0,0],[0,0],[0]],[[409017600,78528000,710400],[78528000,1420800],[710400]],[[0,0,0],[0,0],[0]],[[65318400,28512000,732800],[28512000,1465600],[732800]],[[0,0,0],[0,0],[0]],[[4665600,5875200,424000],[5875200,848000],[424000]],[[0,0,0],[0,0],[0]],[[0,518400,124800],[518400,249600],[124800]],[[0,0,0],[0,0],[0]],[[0,0,14400],[0,28800],[14400]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
