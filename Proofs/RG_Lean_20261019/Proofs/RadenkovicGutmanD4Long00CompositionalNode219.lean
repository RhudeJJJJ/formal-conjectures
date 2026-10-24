/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .scaled (-1) e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[32],[0],[0]],[[0,0],[0,0],[0]],[[992,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[14112,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[122112,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[718272,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[3040448,48,0],[48,0],[0]],[[0,0,0],[0,0],[0]],[[9565088,1072,0],[1072,0],[0]],[[0,0,0],[0,0],[0]],[[22774048,10640,0],[10640,0],[0]],[[0,0,0],[0,0],[0]],[[41403648,61856,0],[61856,0],[0]],[[0,0,0],[0,0],[0]],[[57567328,233744,0],[233744,0],[0]],[[0,0,0],[0,0],[0]],[[60902496,602544,16],[602544,32],[16]],[[0,0,0],[0,0],[0]],[[48417856,1082176,224],[1082176,448],[224]],[[0,0,0],[0,0],[0]],[[28297536,1358992,1296],[1358992,2592],[1296]],[[0,0,0],[0,0],[0]],[[11725056,1179568,4000],[1179568,8000],[4000]],[[0,0,0],[0,0],[0]],[[3239136,687200,7104],[687200,14208],[7104]],[[0,0,0],[0,0],[0]],[[531360,253872,7328],[253872,14656],[7328]],[[0,0,0],[0,0],[0]],[[38880,53136,4240],[53136,8480],[4240]],[[0,0,0],[0,0],[0]],[[0,4752,1248],[4752,2496],[1248]],[[0,0,0],[0,0],[0]],[[0,0,144],[0,288],[144]]]
theorem step219 : p219=NestedHorner.scale (-1) p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_scaled (-1) e219 e218 p218 p219 rfl h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
