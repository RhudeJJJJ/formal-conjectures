/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode033
import Proofs.RadenkovicGutmanD31Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2883],[0,2883]],[[0,0,0],[0,0,0],[0,0]],[[0,-25947,25947],[-25947,95139,12493],[25947,12493]],[[0,0,0],[0,0,0],[0,0]],[[-389205,285417,181629],[285417,651558,15376],[181629,15376]],[[0,0,0],[0,0,0],[0,0]],[[-2464965,4013136,501642],[4013136,1751903,6727],[501642,6727]],[[0,0,0],[0,0,0],[0,0]],[[1349244,18161939,727477],[18161939,2469770,961],[727477,961]],[[0,0,0],[0,0],[0]],[[63486543,44969034,611196],[44969034,2018100],[611196]],[[0,0,0],[0,0],[0]],[[301781869,70644071,306559],[70644071,985986],[306559]],[[0,0,0],[0,0],[0]],[[798754370,75163654,90334],[75163654,283495],[90334]],[[0,0,0],[0,0],[0]],[[1417801740,55861969,14415],[55861969,44206],[14415]],[[0,0,0],[0,0],[0]],[[1810788275,29317227,961],[29317227,2883],[961]],[[0,0],[0]],[[1722400300,10811250],[10811250]],[[0,0],[0]],[[1241846484,2738850],[2738850]],[[0,0],[0]],[[683686152,453592],[453592]],[[0,0],[0]],[[287228485,44206],[44206]],[[0,0],[0]],[[91307493,1922],[1922]],[[0]],[[21570606]],[[0]],[[3667176]],[[0]],[[423801]],[[0]],[[29791]],[[0]],[[961]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
