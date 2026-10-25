/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode033
import Proofs.RadenkovicGutmanD17Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,289]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,6936],[0,6936,34]],[[0,0,0],[0,0,0],[0,0]],[[-23409,-15606,39015],[-15606,150858,21998],[39015,21998]],[[0,0,0],[0,0,0],[0,0]],[[-642600,593028,236844],[593028,902292,23596],[236844,23596]],[[0,0,0],[0,0,0],[0,0]],[[-2770983,5834196,597312],[5834196,2236078,10166],[597312,10166]],[[0,0,0],[0,0,0],[0,0]],[[6561150,23399242,817394],[23399242,3004852,1700],[817394,1700]],[[0,0,0],[0,0,0],[0,0]],[[95066261,54061836,664462],[54061836,2401216,68],[664462,68]],[[0,0,0],[0,0],[0]],[[395535600,81160108,330106],[81160108,1175924],[330106]],[[0,0,0],[0,0],[0]],[[978655082,83777768,99144],[83777768,349758],[99144]],[[0,0,0],[0,0],[0]],[[1663074504,61130266,16966],[61130266,59772],[16966]],[[0,0,0],[0,0],[0]],[[2060552626,31854566,1411],[31854566,5066],[1411]],[[0,0,0],[0,0],[0]],[[1918974756,11812722,34],[11812722,136],[34]],[[0,0],[0]],[[1364898448,3061360],[3061360]],[[0,0],[0]],[[746555544,533460],[533460]],[[0,0],[0]],[[313954929,58004],[58004]],[[0,0],[0]],[[100801704,3366],[3366]],[[0,0],[0]],[[24341586,68],[68]],[[0]],[[4307392]],[[0]],[[534769]],[[0]],[[43180]],[[0]],[[1955]],[[0]],[[34]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
