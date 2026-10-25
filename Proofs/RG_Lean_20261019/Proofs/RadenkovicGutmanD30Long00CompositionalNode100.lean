/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode043
import Proofs.RadenkovicGutmanD30Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-8100],[0,-16200,5040],[-8100,5040]],[[0,0,0],[0,0,0],[0,0]],[[0,-319140,-24840],[-319140,25920,21840],[-24840,21840]],[[0,0,0],[0,0,0],[0,0]],[[-2964600,-2574180,79020],[-2574180,662040,26880],[79020,26880]],[[0,0,0],[0,0,0],[0,0]],[[-35688600,-7733340,464760],[-7733340,2238240,11760],[464760,11760]],[[0,0,0],[0,0,0],[0,0]],[[-190003320,-8375880,872160],[-8375880,3518400,1680],[872160,1680]],[[0,0,0],[0,0],[0]],[[-589438800,9363780,843480],[9363780,3078000],[843480]],[[0,0,0],[0,0],[0]],[[-1173040080,43267260,463020],[43267260,1577880],[463020]],[[0,0,0],[0,0],[0]],[[-1530934320,67150800,145320],[67150800,470400],[145320]],[[0,0,0],[0,0],[0]],[[-1225310040,61684980,24300],[61684980,75480],[24300]],[[0,0,0],[0,0],[0]],[[-355558920,37221660,1680],[37221660,5040],[1680]],[[0,0],[0]],[[464598720,15167640],[15167640]],[[0,0],[0]],[[762888600,4142700],[4142700]],[[0,0],[0]],[[600833880,727620],[727620]],[[0,0],[0]],[[312288480,74340],[74340]],[[0,0],[0]],[[114570000,3360],[3360]],[[0]],[[30016800]],[[0]],[[5518200]],[[0]],[[677880]],[[0]],[[50040]],[[0]],[[1680]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
