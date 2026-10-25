/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode043
import Proofs.RadenkovicGutmanD14Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-588],[0,-588,336]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-5292,-8820],[-5292,-29232,5432],[-8820,5432,48]],[[0,0,0],[0,0,0],[0,0]],[[-131544,-362124,-23016],[-362124,-45840,22228],[-23016,22228]],[[0,0,0],[0,0,0],[0,0]],[[-4394520,-2589336,64564],[-2589336,382672,26020],[64564,26020]],[[0,0,0],[0,0,0],[0,0]],[[-41370048,-7607968,355588],[-7607968,1547808,11800],[355588,11800]],[[0,0,0],[0,0,0],[0,0]],[[-199278624,-9661072,638660],[-9661072,2537904,2084],[638660,2084]],[[0,0,0],[0,0,0],[0,0]],[[-589948120,1873728,604356],[1873728,2279952,96],[604356,96]],[[0,0,0],[0,0],[0]],[[-1160552264,25792576,332188],[25792576,1211184],[332188]],[[0,0,0],[0,0],[0]],[[-1559131392,43617844,107596],[43617844,384064],[107596]],[[0,0,0],[0,0],[0]],[[-1399204024,41379016,19632],[41379016,69568],[19632]],[[0,0,0],[0,0],[0]],[[-721825584,25578008,1748],[25578008,6304],[1748]],[[0,0,0],[0,0],[0]],[[-432880,10729068,48],[10729068,192],[48]],[[0,0],[0]],[[359641544,3059196],[3059196]],[[0,0],[0]],[[350700128,576996],[576996]],[[0,0],[0]],[[199585576,67396],[67396]],[[0,0],[0]],[[77870072,4220],[4220]],[[0,0],[0]],[[21615568,96],[96]],[[0]],[[4257224]],[[0]],[[577080]],[[0]],[[50392]],[[0]],[[2472]],[[0]],[[48]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
