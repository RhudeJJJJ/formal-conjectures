/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,75],[0,75]],[[0,0,0],[0,0,0],[0,0]],[[0,675,1125],[675,3600,355],[1125,355]],[[0,0,0],[0,0,0],[0,0]],[[12150,42120,8895],[42120,27780,530],[8895,530]],[[0,0,0],[0,0,0],[0,0]],[[426060,401850,28190],[401850,86260,335],[28190,335]],[[0,0,0],[0,0,0],[0,0]],[[4458780,1773700,47045],[1773700,142380,95],[47045,95]],[[0,0,0],[0,0,0],[0,0]],[[24201360,4584290,45670],[4584290,138280,10],[45670,10]],[[0,0,0],[0,0],[0]],[[82072830,7681610,26835],[7681610,82340],[26835]],[[0,0,0],[0,0],[0]],[[190494980,8800380,9590],[8800380,30260],[9590]],[[0,0,0],[0,0],[0]],[[318856640,7094025,2015],[7094025,6660],[2015]],[[0,0,0],[0,0],[0]],[[397515210,4077645,225],[4077645,800],[225]],[[0,0,0],[0,0],[0]],[[376680890,1673045,10],[1673045,40],[10]],[[0,0],[0]],[[274621090,484340],[484340]],[[0,0],[0]],[[154949040,96175],[96175]],[[0,0],[0]],[[67683700,12390],[12390]],[[0,0],[0]],[[22766570,925],[925]],[[0,0],[0]],[[5826200,30],[30]],[[0]],[[1110560]],[[0]],[[152210]],[[0]],[[14120]],[[0]],[[790]],[[0]],[[20]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
