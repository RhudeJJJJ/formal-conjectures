/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,625]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-11250,11250],[0,11250]],[[0,0,0],[0,0,0],[0,0]],[[50625,-101250,50625],[-101250,105000,30000],[50625,30000]],[[0,0,0],[0,0,0],[0,0]],[[-33750,-236250,270000],[-236250,748750,27500],[270000,27500]],[[0,0,0],[0,0,0],[0,0]],[[-1873125,1721250,607500],[1721250,1857500,10000],[607500,10000]],[[0,0,0],[0,0,0],[0,0]],[[-5156250,10785000,750000],[10785000,2445000,1250],[750000,1250]],[[0,0,0],[0,0],[0]],[[10853125,28536250,553750],[28536250,1902500],[553750]],[[0,0,0],[0,0],[0]],[[102977500,45643750,250000],[45643750,898750],[250000]],[[0,0,0],[0,0],[0]],[[321733750,48807500,67500],[48807500,252500],[67500]],[[0,0,0],[0,0],[0]],[[618633750,36320000,10000],[36320000,38750],[10000]],[[0,0,0],[0,0],[0]],[[832615000,19066250,625],[19066250,2500],[625]],[[0,0],[0]],[[825645000,7031250],[7031250]],[[0,0],[0]],[[617795000,1781250],[1781250]],[[0,0],[0]],[[352281250,295000],[295000]],[[0,0],[0]],[[153148125,28750],[28750]],[[0,0],[0]],[[50352500,1250],[1250]],[[0]],[[12298750]],[[0]],[[2161250]],[[0]],[[258125]],[[0]],[[18750]],[[0]],[[625]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
