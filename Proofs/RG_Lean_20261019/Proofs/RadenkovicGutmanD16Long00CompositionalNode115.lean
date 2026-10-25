/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode113
import Proofs.RadenkovicGutmanD16Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,256]],[[0,0],[0,0,0],[0,0]],[[0,0,2304],[0,0,4608],[2304,4608]],[[0,0,0],[0,0,0],[0,0]],[[20736,41472,40704],[41472,82944,12288],[40704,12288]],[[0,0,0],[0,0,0],[0,0]],[[732672,843264,178432],[843264,442368,11264],[178432,11264]],[[0,0,0],[0,0,0],[0,0]],[[9683712,5266944,366080],[5266944,995328,4096],[366080,4096]],[[0,0,0],[0,0,0],[0,0]],[[63330816,16982016,420864],[16982016,1228800,512],[420864,512]],[[0,0,0],[0,0],[0]],[[248356096,33654272,290816],[33654272,907264],[290816]],[[0,0,0],[0,0],[0]],[[649384960,44480000,123136],[44480000,409600],[123136]],[[0,0,0],[0,0],[0]],[[1204874752,40907776,31232],[40907776,110592],[31232]],[[0,0,0],[0,0],[0]],[[1648787968,26734592,4352],[26734592,16384],[4352]],[[0,0,0],[0,0],[0]],[[1705295872,12490240,256],[12490240,1024],[256]],[[0,0],[0]],[[1353297920,4139520],[4139520]],[[0,0],[0]],[[830709760,949760],[949760]],[[0,0],[0]],[[395259392,143360],[143360]],[[0,0],[0]],[[145229056,12800],[12800]],[[0,0],[0]],[[40774656,512],[512]],[[0]],[[8578560]],[[0]],[[1308160]],[[0]],[[136448]],[[0]],[[8704]],[[0]],[[256]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
