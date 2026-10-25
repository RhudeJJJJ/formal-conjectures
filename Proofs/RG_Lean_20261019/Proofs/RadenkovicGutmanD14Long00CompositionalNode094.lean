/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode035
import Proofs.RadenkovicGutmanD14Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-1764],[0,-3528,1008],[-1764,1008]],[[0,0,0],[0,0,0],[0,0]],[[0,-49140,-6216],[-49140,5712,4368],[-6216,4368]],[[0,0,0],[0,0,0],[0,0]],[[-312984,-288036,11564],[-288036,150136,5376],[11564,5376]],[[0,0,0],[0,0,0],[0,0]],[[-2481192,-85932,85624],[-85932,522032,2352],[85624,2352]],[[0,0,0],[0,0,0],[0,0]],[[-3681720,3548104,167328],[3548104,843360,336],[167328,336]],[[0,0,0],[0,0],[0]],[[31191552,13514228,164696],[13514228,756784],[164696]],[[0,0,0],[0,0],[0]],[[194032272,25865756,91308],[25865756,396984],[91308]],[[0,0,0],[0,0],[0]],[[562366448,30937424,28840],[30937424,120848],[28840]],[[0,0,0],[0,0],[0]],[[1043633640,24833508,4844],[24833508,19768],[4844]],[[0,0,0],[0,0],[0]],[[1363624136,13747468,336],[13747468,1344],[336]],[[0,0],[0]],[[1310039136,5266408],[5266408]],[[0,0],[0]],[[946078616,1371580],[1371580]],[[0,0],[0]],[[518808472,231812],[231812]],[[0,0],[0]],[[216297424,22932],[22932]],[[0,0],[0]],[[68067888,1008],[1008]],[[0]],[[15894144]],[[0]],[[2668344]],[[0]],[[304360]],[[0]],[[21112]],[[0]],[[672]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
