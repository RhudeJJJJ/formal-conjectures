/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode093
import Proofs.RadenkovicGutmanD44Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1936]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-17424],[0,-34848,57552],[-17424,57552,88]],[[0,0,0],[0,0,0],[0,0]],[[-156816,-579744,210144],[-579744,1107744,192896],[210144,192896]],[[0,0,0],[0,0,0],[0,0]],[[-7201656,1534896,1760792],[1534896,7767232,210496],[1760792,210496]],[[0,0,0],[0,0,0],[0,0]],[[-38353392,41424768,4983616],[41424768,20681760,87824],[4983616,87824]],[[0,0,0],[0,0,0],[0,0]],[[48592104,203598560,7278128],[203598560,29058304,12848],[7278128,12848]],[[0,0,0],[0,0,0],[0,0]],[[1138320656,521192144,6150144],[521192144,23849408,176],[6150144,176]],[[0,0,0],[0,0],[0]],[[5145950568,834520368,3109744],[834520368,11784608],[3109744]],[[0,0,0],[0,0],[0]],[[13307439904,899170096,928576],[899170096,3454880],[928576]],[[0,0,0],[0,0],[0]],[[23229097584,674338720,152064],[674338720,557920],[152064]],[[0,0,0],[0,0],[0]],[[29230052544,356469696,10912],[356469696,39776],[10912]],[[0,0,0],[0,0],[0]],[[27407998464,132372592,88],[132372592,352],[88]],[[0,0],[0]],[[19486586592,33825440],[33825440]],[[0,0],[0]],[[10585027552,5679872],[5679872]],[[0,0],[0]],[[4392015760,569360],[569360]],[[0,0],[0]],[[1381160616,26928],[26928]],[[0,0],[0]],[[323591136,176],[176]],[[0]],[[54784048]],[[0]],[[6353072]],[[0]],[[456104]],[[0]],[[16016]],[[0]],[[88]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
