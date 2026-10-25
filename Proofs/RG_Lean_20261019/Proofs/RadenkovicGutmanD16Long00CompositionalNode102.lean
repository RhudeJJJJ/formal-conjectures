/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode100
import Proofs.RadenkovicGutmanD16Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,256]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-2304],[0,-4608,7488],[-2304,7488,32]],[[0,0,0],[0,0,0],[0,0]],[[-20736,-77760,26688],[-77760,143232,25344],[26688,25344]],[[0,0,0],[0,0,0],[0,0]],[[-963360,169344,226784],[169344,1012864,28160],[226784,28160]],[[0,0,0],[0,0,0],[0,0]],[[-5315328,5258304,646528],[5258304,2718848,12224],[646528,12224]],[[0,0,0],[0,0,0],[0,0]],[[4670304,26279424,951360],[26279424,3856896,1984],[951360,1984]],[[0,0,0],[0,0,0],[0,0]],[[144273536,67950080,811776],[67950080,3204608,64],[811776,64]],[[0,0,0],[0,0],[0]],[[668524768,109745792,416256],[109745792,1610496],[416256]],[[0,0,0],[0,0],[0]],[[1750630912,119277376,127104],[119277376,484480],[127104]],[[0,0,0],[0,0],[0]],[[3084357824,90300608,21696],[90300608,81920],[21696]],[[0,0,0],[0,0],[0]],[[3912626304,48260288,1728],[48260288,6528],[1728]],[[0,0,0],[0,0],[0]],[[3696976640,18166080,32],[18166080,128],[32]],[[0,0],[0]],[[2648921600,4727360],[4727360]],[[0,0],[0]],[[1450793472,815680],[815680]],[[0,0],[0]],[[607559552,85760],[85760]],[[0,0],[0]],[[193160160,4544],[4544]],[[0,0],[0]],[[45883392,64],[64]],[[0]],[[7915200]],[[0]],[[944256]],[[0]],[[71264]],[[0]],[[2816]],[[0]],[[32]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
