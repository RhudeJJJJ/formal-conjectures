/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode051
import Proofs.RadenkovicGutmanD43Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1849]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,44376],[0,44376,86]],[[0,0,0],[0,0,0],[0,0]],[[-149769,99846,249615],[99846,1000008,138374],[249615,138374]],[[0,0,0],[0,0,0],[0,0]],[[-791802,6703614,1504656],[6703614,6032040,144652],[1504656,144652]],[[0,0,0],[0,0,0],[0,0]],[[36639999,55132020,3764736],[55132020,15104524,59254],[3764736,59254]],[[0,0,0],[0,0,0],[0,0]],[[437161650,210750740,5101778],[210750740,20485888,8772],[5101778,8772]],[[0,0,0],[0,0,0],[0,0]],[[2304862307,477222084,4093342],[477222084,16449736,172],[4093342,172]],[[0,0,0],[0,0],[0]],[[7361133106,707354386,1995458],[707354386,8024832],[1995458]],[[0,0,0],[0,0],[0]],[[15966939998,721267896,581704],[721267896,2340748],[581704]],[[0,0,0],[0,0],[0]],[[24929758088,518567530,94342],[518567530,379776],[94342]],[[0,0,0],[0,0],[0]],[[28970505068,265108330,6923],[265108330,27864],[6923]],[[0,0,0],[0,0],[0]],[[25558409832,95847172,86],[95847172,344],[86]],[[0,0],[0]],[[17304893340,23985400],[23985400]],[[0,0],[0]],[[9028016840,3968986],[3968986]],[[0,0],[0]],[[3620837747,395772],[395772]],[[0,0],[0]],[[1106275362,19092],[19092]],[[0,0],[0]],[[252939846,172],[172]],[[0]],[[41969720]],[[0]],[[4793855]],[[0]],[[341678]],[[0]],[[12169]],[[0]],[[86]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
