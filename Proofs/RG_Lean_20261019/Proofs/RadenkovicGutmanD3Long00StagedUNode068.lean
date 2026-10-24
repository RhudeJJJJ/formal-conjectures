/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode065
import Proofs.RadenkovicGutmanD3Long00StagedUNode067
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e068 : NestedArithmetic.Expr 3 := .plus e065 e067
noncomputable def p068 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,9]],[[0,0],[0,0,0],[0,0,0]],[[0,0,81],[0,162,234],[81,234,16]],[[0,0,0],[0,0,0],[0,0,0]],[[-729,3321,2403],[3321,7416,1104],[2403,1104,4]],[[0,0,0],[0,0,0],[0,0]],[[18306,78975,15561],[78975,50574,1932],[15561,1932]],[[0,0,0],[0,0,0],[0,0]],[[589869,617571,46710],[617571,154964,1592],[46710,1592]],[[0,0,0],[0,0,0],[0,0]],[[5640354,2522166,79260],[2522166,267684,642],[79260,642]],[[0,0,0],[0,0,0],[0,0]],[[29100963,6360159,82728],[6360159,285508,120],[82728,120]],[[0,0,0],[0,0,0],[0,0]],[[96397912,10754915,55225],[10754915,195666,8],[55225,8]],[[0,0,0],[0,0],[0]],[[222972986,12770140,23870],[12770140,87100],[23870]],[[0,0,0],[0,0],[0]],[[377996882,10932171,6601],[10932171,24830],[6601]],[[0,0,0],[0,0],[0]],[[484072250,6840717,1117],[6840717,4324],[1117]],[[0,0,0],[0,0],[0]],[[477452288,3140892,104],[3140892,412],[104]],[[0,0,0],[0,0],[0]],[[367084986,1052245,4],[1052245,16],[4]],[[0,0],[0]],[[221420706,252923],[252923]],[[0,0],[0]],[[104956563,42211],[42211]],[[0,0],[0]],[[38980032,4606],[4606]],[[0,0],[0]],[[11250358,292],[292]],[[0,0],[0]],[[2486574,8],[8]],[[0]],[[410941]],[[0]],[[48870]],[[0]],[[3921]],[[0]],[[188]],[[0]],[[4]]]
theorem step068 : p068=NestedHorner.add p065 p067 := by decide +kernel
#print axioms step068
theorem h068 : NestedArithmetic.compile e068=p068 := StagedExprCompile.compile_plus e068 e065 e067 p065 p067 p068 rfl h065 h067 step068
#print axioms h068
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
