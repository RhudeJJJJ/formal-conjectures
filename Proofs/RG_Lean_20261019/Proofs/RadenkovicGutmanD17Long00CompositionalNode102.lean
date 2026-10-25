/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode100
import Proofs.RadenkovicGutmanD17Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,289]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-2601],[0,-5202,8466],[-2601,8466,34]],[[0,0,0],[0,0,0],[0,0]],[[-23409,-87669,30243],[-87669,162078,28628],[30243,28628]],[[0,0,0],[0,0,0],[0,0]],[[-1085994,195075,256649],[195075,1145290,31756],[256649,31756]],[[0,0,0],[0,0,0],[0,0]],[[-5964705,5963481,731170],[5963481,3072274,13736],[731170,13736]],[[0,0,0],[0,0,0],[0,0]],[[5557776,29755712,1075148],[29755712,4354788,2210],[1075148,2210]],[[0,0,0],[0,0,0],[0,0]],[[164074565,76869869,916572],[76869869,3614540,68],[916572,68]],[[0,0,0],[0,0],[0]],[[757830760,124059931,469387],[124059931,1813866],[469387]],[[0,0,0],[0,0],[0]],[[1981658006,134735744,143038],[134735744,544442],[143038]],[[0,0,0],[0,0],[0]],[[3488069554,101922021,24327],[101922021,91698],[24327]],[[0,0,0],[0,0],[0]],[[4421332392,54420315,1921],[54420315,7242],[1921]],[[0,0,0],[0,0],[0]],[[4174705504,20460894,34],[20460894,136],[34]],[[0,0],[0]],[[2989142130,5316155],[5316155]],[[0,0],[0]],[[1635933086,915127],[915127]],[[0,0],[0]],[[684533373,95829],[95829]],[[0,0],[0]],[[217422656,5032],[5032]],[[0,0],[0]],[[51584154,68],[68]],[[0]],[[8884030]],[[0]],[[1057247]],[[0]],[[79458]],[[0]],[[3111]],[[0]],[[34]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
