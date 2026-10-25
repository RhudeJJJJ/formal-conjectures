/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode100
import Proofs.RadenkovicGutmanD6Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,36]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-324],[0,-648,1008],[-324,1008,12]],[[0,0,0],[0,0,0],[0,0]],[[-2916,-11340,3348],[-11340,18792,3504],[3348,3504]],[[0,0,0],[0,0,0],[0,0]],[[-140940,10044,29664],[10044,135864,4080],[29664,4080]],[[0,0,0],[0,0,0],[0,0]],[[-873828,642924,86328],[642924,371928,1944],[86328,1944]],[[0,0,0],[0,0,0],[0,0]],[[-350676,3382464,129720],[3382464,539856,384],[129720,384]],[[0,0,0],[0,0,0],[0,0]],[[16041636,8988660,113616],[8988660,461808,24],[113616,24]],[[0,0,0],[0,0],[0]],[[82967868,14842812,60396],[14842812,241416],[60396]],[[0,0,0],[0,0],[0]],[[227265432,16481256,19464],[16481256,76920],[19464]],[[0,0,0],[0,0],[0]],[[412142304,12765228,3636],[12765228,14280],[3636]],[[0,0,0],[0,0],[0]],[[534880944,7001988,348],[7001988,1368],[348]],[[0,0,0],[0,0],[0]],[[515773920,2720160,12],[2720160,48],[12]],[[0,0],[0]],[[376888200,737460],[737460]],[[0,0],[0]],[[210641592,134820],[134820]],[[0,0],[0]],[[90183012,15540],[15540]],[[0,0],[0]],[[29411580,984],[984]],[[0,0],[0]],[[7207272,24],[24]],[[0]],[[1294800]],[[0]],[[163596]],[[0]],[[13524]],[[0]],[[636]],[[0]],[[12]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
