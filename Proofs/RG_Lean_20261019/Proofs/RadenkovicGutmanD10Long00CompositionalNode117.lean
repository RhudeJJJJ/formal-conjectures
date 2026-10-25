/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode112
import Proofs.RadenkovicGutmanD10Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,240],[0,240,296]],[[0,0,0],[0,0,0],[0,0,0]],[[0,2160,5760],[2160,8928,6608],[5760,6608,4]],[[0,0,0],[0,0,0],[0,0]],[[82296,155952,72456],[155952,167592,16600],[72456,16600]],[[0,0,0],[0,0,0],[0,0]],[[2357316,2002392,291076],[2002392,749408,15056],[291076,15056]],[[0,0,0],[0,0,0],[0,0]],[[25792560,10741400,574960],[10741400,1583816,5552],[574960,5552]],[[0,0,0],[0,0,0],[0,0]],[[150811404,32169752,648128],[32169752,1899984,736],[648128,736]],[[0,0,0],[0,0,0],[0,0]],[[551594720,61106656,443456],[61106656,1385376,8],[443456,8]],[[0,0,0],[0,0],[0]],[[1376854804,78643688,187384],[78643688,624528],[187384]],[[0,0,0],[0,0],[0]],[[2472551232,71089416,47888],[71089416,170248],[47888]],[[0,0,0],[0,0],[0]],[[3303478776,45955376,6848],[45955376,25936],[6848]],[[0,0,0],[0,0],[0]],[[3355614504,21345888,440],[21345888,1768],[440]],[[0,0,0],[0,0],[0]],[[2626574368,7068600,4],[7068600,16],[4]],[[0,0],[0]],[[1595615520,1630360],[1630360]],[[0,0],[0]],[[753533312,249800],[249800]],[[0,0],[0]],[[275569584,23120],[23120]],[[0,0],[0]],[[77244020,1032],[1032]],[[0,0],[0]],[[16288864,8],[8]],[[0]],[[2504280]],[[0]],[[266128]],[[0]],[[17716]],[[0]],[[592]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
