/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode219
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e219 e003
noncomputable def p220 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[32,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[992,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[14112,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[122112,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[718272,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[3040448,48,0],[48,0],[0]],[[0,0,0],[0,0],[0]],[[9565088,1072,0],[1072,0],[0]],[[0,0,0],[0,0],[0]],[[22774048,10640,0],[10640,0],[0]],[[0,0,0],[0,0],[0]],[[41403648,61856,0],[61856,0],[0]],[[0,0,0],[0,0],[0]],[[57567328,233744,0],[233744,0],[0]],[[0,0,0],[0,0],[0]],[[60902496,602544,16],[602544,32],[16]],[[0,0,0],[0,0],[0]],[[48417856,1082176,224],[1082176,448],[224]],[[0,0,0],[0,0],[0]],[[28297536,1358992,1296],[1358992,2592],[1296]],[[0,0,0],[0,0],[0]],[[11725056,1179568,4000],[1179568,8000],[4000]],[[0,0,0],[0,0],[0]],[[3239136,687200,7104],[687200,14208],[7104]],[[0,0,0],[0,0],[0]],[[531360,253872,7328],[253872,14656],[7328]],[[0,0,0],[0,0],[0]],[[38880,53136,4240],[53136,8480],[4240]],[[0,0,0],[0,0],[0]],[[0,4752,1248],[4752,2496],[1248]],[[0,0,0],[0,0],[0]],[[0,0,144],[0,288],[144]]]
theorem step220 : p220=NestedArithmetic.mul p219 p003 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e219 e003 p219 p003 p220 rfl h219 h003 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
