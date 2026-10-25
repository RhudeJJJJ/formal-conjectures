/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode043
import Proofs.RadenkovicGutmanD14Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-1764],[0,-3528,1008],[-1764,1008]],[[0,0,0],[0,0,0],[0,0]],[[0,-70308,-6216],[-70308,2688,4368],[-6216,4368]],[[0,0,0],[0,0,0],[0,0]],[[-657720,-590436,11564],[-590436,123928,5376],[11564,5376]],[[0,0,0],[0,0,0],[0,0]],[[-8066520,-1925532,85624],[-1925532,432992,2352],[85624,2352]],[[0,0,0],[0,0,0],[0,0]],[[-43949304,-2754696,167328],[-2754696,689472,336],[167328,336]],[[0,0,0],[0,0],[0]],[[-140516880,-79996,164696],[-79996,607600],[164696]],[[0,0,0],[0,0],[0]],[[-291938192,6284348,91308],[6284348,312984],[91308]],[[0,0,0],[0,0],[0]],[[-408950192,11447632,28840],[11447632,93632],[28840]],[[0,0,0],[0,0],[0]],[[-380128728,11180148,4844],[11180148,15064],[4844]],[[0,0,0],[0,0],[0]],[[-204140104,6975388,336],[6975388,1008],[336]],[[0,0],[0]],[[-6486592,2904216],[2904216]],[[0,0],[0]],[[95926040,805420],[805420]],[[0,0],[0]],[[95578840,143108],[143108]],[[0,0],[0]],[[54400416,14756],[14756]],[[0,0],[0]],[[20955984,672],[672]],[[0]],[[5661600]],[[0]],[[1063160]],[[0]],[[132664]],[[0]],[[9912]],[[0]],[[336]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
