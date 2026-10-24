/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode067
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e068 : NestedArithmetic.Expr 3 := .scaled (-1) e067
noncomputable def p068 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,480],[0,480,16]],[[0,0,0],[0,0,0],[0,0,0]],[[-1296,0,3600],[0,13104,1984],[3600,1984,4]],[[0,0,0],[0,0,0],[0,0]],[[-19872,88560,26160],[88560,93336,2984],[26160,2984]],[[0,0,0],[0,0,0],[0,0]],[[414612,892728,79204],[892728,278032,2112],[79204,2112]],[[0,0,0],[0,0,0],[0,0]],[[6554328,3973032,130944],[3973032,455704,752],[130944,752]],[[0,0,0],[0,0,0],[0,0]],[[40216172,10342120,130608],[10342120,454832,128],[130608,128]],[[0,0,0],[0,0,0],[0,0]],[[145065496,17586192,82144],[17586192,289024,8],[82144,8]],[[0,0,0],[0,0],[0]],[[351269764,20659528,33080],[20659528,118656],[33080]],[[0,0,0],[0,0],[0]],[[609515216,17288248,8448],[17288248,31128],[8448]],[[0,0,0],[0,0],[0]],[[786954760,10468816,1312],[10468816,4992],[1312]],[[0,0,0],[0,0],[0]],[[773711736,4610000,112],[4610000,440],[112]],[[0,0,0],[0,0],[0]],[[587495232,1468936,4],[1468936,16],[4]],[[0,0],[0]],[[347194656,333208],[333208]],[[0,0],[0]],[[160087744,52104],[52104]],[[0,0],[0]],[[57449544,5296],[5296]],[[0,0],[0]],[[15920484,312],[312]],[[0,0],[0]],[[3358064,8],[8]],[[0]],[[526520]],[[0]],[[59080]],[[0]],[[4452]],[[0]],[[200]],[[0]],[[4]]]
theorem step068 : p068=NestedHorner.scale (-1) p067 := by decide +kernel
#print axioms step068
theorem h068 : NestedArithmetic.compile e068=p068 := StagedExprCompile.compile_scaled (-1) e068 e067 p067 p068 rfl h067 step068
#print axioms h068
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
