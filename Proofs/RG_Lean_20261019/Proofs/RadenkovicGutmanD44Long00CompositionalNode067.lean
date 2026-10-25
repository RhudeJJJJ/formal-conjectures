/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode043
import Proofs.RadenkovicGutmanD44Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,17424],[0,34848,-22176],[17424,-22176,7056]],[[0,0,0],[0,0,0],[0,0]],[[0,584496,-48576],[584496,-469104,30912],[-48576,30912]],[[0,0,0],[0,0,0],[0,0]],[[3921696,1409184,-312512],[1409184,-2040256,220416],[-312512,220416]],[[0,0,0],[0,0,0],[0,0]],[[20313072,-7621776,76256],[-7621776,-666992,258720],[76256,258720]],[[0,0,0],[0,0,0],[0,0]],[[-38769840,-36863664,2122272],[-36863664,8154912,105504],[2122272,105504]],[[0,0,0],[0,0,0],[0,0]],[[-620847984,-46906544,4249888],[-46906544,17374208,14112],[4249888,14112]],[[0,0,0],[0,0],[0]],[[-2413210336,41113792,4050384],[41113792,16643904],[4050384]],[[0,0,0],[0,0],[0]],[[-5171930464,214400288,2154656],[214400288,8809360],[2154656]],[[0,0,0],[0,0],[0]],[[-6823999872,332292912,653104],[332292912,2650880],[653104]],[[0,0,0],[0,0],[0]],[[-5204094704,299777072,105504],[299777072,425040],[105504]],[[0,0,0],[0,0],[0]],[[-946522400,176694576,7056],[176694576,28224],[7056]],[[0,0],[0]],[[2843789440,70212560],[70212560]],[[0,0],[0]],[[3986408864,18697408],[18697408]],[[0,0],[0]],[[2976776880,3203536],[3203536]],[[0,0],[0]],[[1495201632,319536],[319536]],[[0,0],[0]],[[533742816,14112],[14112]],[[0]],[[136526080]],[[0]],[[24555440]],[[0]],[[2955648]],[[0]],[[214032]],[[0]],[[7056]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
