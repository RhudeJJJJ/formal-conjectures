/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode067
import Proofs.RadenkovicGutmanD12Long00CompositionalNode069
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .plus e067 e069
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,144]],[[0,0],[0,0,0],[0,0,0]],[[0,0,1296],[0,2592,2880],[1296,2880,448]],[[0,0,0],[0,0,0],[0,0,0]],[[-11664,45360,30672],[45360,88416,16512],[30672,16512,4]],[[0,0,0],[0,0,0],[0,0]],[[145152,952560,202320],[952560,630264,30696],[202320,30696]],[[0,0,0],[0,0,0],[0,0]],[[5787396,7348104,620676],[7348104,2000000,24416],[620676,24416]],[[0,0,0],[0,0,0],[0,0]],[[57270888,30107544,1060512],[30107544,3502680,8400],[1060512,8400]],[[0,0,0],[0,0,0],[0,0]],[[300486684,76146456,1094544],[76146456,3705328,1056],[1094544,1056]],[[0,0,0],[0,0,0],[0,0]],[[1005143896,128519024,706672],[128519024,2457600,8],[706672,8]],[[0,0,0],[0,0],[0]],[[2336466692,151310920,286616],[151310920,1026160],[286616]],[[0,0,0],[0,0],[0]],[[3964292816,127420584,70960],[127420584,261944],[70960]],[[0,0,0],[0,0],[0]],[[5061421688,77670528,9856],[77670528,37552],[9856]],[[0,0,0],[0,0],[0]],[[4957173560,34305696,608],[34305696,2392],[608]],[[0,0,0],[0,0],[0]],[[3767697600,10866232,4],[10866232,16],[4]],[[0,0],[0]],[[2234871168,2406776],[2406776]],[[0,0],[0]],[[1035025104,354808],[354808]],[[0,0],[0]],[[372436872,31552],[31552]],[[0,0],[0]],[[102974884,1336],[1336]],[[0,0],[0]],[[21454704,8],[8]],[[0]],[[3261448]],[[0]],[[342504]],[[0]],[[22452]],[[0]],[[728]],[[0]],[[4]]]
theorem step070 : p070=NestedHorner.add p067 p069 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_plus e070 e067 e069 p067 p069 p070 rfl h067 h069 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
