/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode033
import Proofs.RadenkovicGutmanD18Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,972],[0,972]],[[0,0,0],[0,0,0],[0,0]],[[0,-8748,8748],[-8748,32076,4212],[8748,4212]],[[0,0,0],[0,0,0],[0,0]],[[-131220,96228,61236],[96228,219672,5184],[61236,5184]],[[0,0,0],[0,0,0],[0,0]],[[-831060,1353024,169128],[1353024,590652,2268],[169128,2268]],[[0,0,0],[0,0,0],[0,0]],[[454896,6123276,245268],[6123276,832680,324],[245268,324]],[[0,0,0],[0,0],[0]],[[21404412,15161256,206064],[15161256,680400],[206064]],[[0,0,0],[0,0],[0]],[[101745396,23817564,103356],[23817564,332424],[103356]],[[0,0,0],[0,0],[0]],[[269299080,25341336,30456],[25341336,95580],[30456]],[[0,0,0],[0,0],[0]],[[478010160,18833796,4860],[18833796,14904],[4860]],[[0,0,0],[0,0],[0]],[[610505100,9884268,324],[9884268,972],[324]],[[0,0],[0]],[[580705200,3645000],[3645000]],[[0,0],[0]],[[418687056,923400],[923400]],[[0,0],[0]],[[230503968,152928],[152928]],[[0,0],[0]],[[96838740,14904],[14904]],[[0,0],[0]],[[30784212,648],[648]],[[0]],[[7272504]],[[0]],[[1236384]],[[0]],[[142884]],[[0]],[[10044]],[[0]],[[324]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
