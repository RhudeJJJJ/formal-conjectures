/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode033
import Proofs.RadenkovicGutmanD25Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,625]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,11250],[0,11250]],[[0,0,0],[0,0,0],[0,0]],[[-50625,0,50625],[0,202500,30000],[50625,30000]],[[0,0,0],[0,0,0],[0,0]],[[-877500,911250,270000],[911250,1080000,27500],[270000,27500]],[[0,0,0],[0,0,0],[0,0]],[[-2683125,7290000,607500],[7290000,2430000,10000],[607500,10000]],[[0,0,0],[0,0,0],[0,0]],[[12750000,26122500,750000],[26122500,3000000,1250],[750000,1250]],[[0,0,0],[0,0],[0]],[[121514375,55350000,553750],[55350000,2215000],[553750]],[[0,0,0],[0,0],[0]],[[448565000,77118750,250000],[77118750,1000000],[250000]],[[0,0,0],[0,0],[0]],[[1024733750,74340000,67500],[74340000,270000],[67500]],[[0,0,0],[0,0],[0]],[[1631882500,50795000,10000],[50795000,40000],[10000]],[[0,0,0],[0,0],[0]],[[1908882500,24780000,625],[24780000,2500],[625]],[[0,0],[0]],[[1685082500,8568750],[8568750]],[[0,0],[0]],[[1138220000,2050000],[2050000]],[[0,0],[0]],[[591325000,322500],[322500]],[[0,0],[0]],[[235794375,30000],[30000]],[[0,0],[0]],[[71490000,1250],[1250]],[[0]],[[16173750]],[[0]],[[2642500]],[[0]],[[294375]],[[0]],[[20000]],[[0]],[[625]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
