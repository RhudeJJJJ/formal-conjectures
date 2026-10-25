/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,5625],[0,11250],[5625]],[[0,0,0],[0,0],[0]],[[0,185625,48750],[185625,97500],[48750]],[[0,0,0],[0,0],[0]],[[1518750,2075625,165625],[2075625,331250],[165625]],[[0,0,0],[0,0],[0]],[[20756250,9916875,286250],[9916875,572500],[286250]],[[0,0,0],[0,0],[0]],[[126528750,26843750,277500],[26843750,555000],[277500]],[[0,0,0],[0,0],[0]],[[458010000,46076875,156250],[46076875,312500],[156250]],[[0,0,0],[0,0],[0]],[[1105372500,53085625,50625],[53085625,101250],[50625]],[[0,0,0],[0,0],[0]],[[1891322500,42272500,8750],[42272500,17500],[8750]],[[0,0,0],[0,0],[0]],[[2379003750,23536875,625],[23536875,1250],[625]],[[0,0],[0]],[[2248723750,9130625],[9130625]],[[0,0],[0]],[[1617330000,2416250],[2416250]],[[0,0],[0]],[[889611250,415625],[415625]],[[0,0],[0]],[[373636250,41875],[41875]],[[0,0],[0]],[[118767500,1875],[1875]],[[0]],[[28057500]],[[0]],[[4770000]],[[0]],[[551250]],[[0]],[[38750]],[[0]],[[1250]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
