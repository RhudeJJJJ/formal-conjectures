/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode100
import Proofs.RadenkovicGutmanD42Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1764]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-15876],[0,-31752,52416],[-15876,52416,84]],[[0,0,0],[0,0,0],[0,0]],[[-142884,-528444,191268],[-528444,1011528,175728],[191268,175728]],[[0,0,0],[0,0,0],[0,0]],[[-6538644,1417500,1603224],[1417500,7098840,191856],[1603224,191856]],[[0,0,0],[0,0,0],[0,0]],[[-34326180,37989756,4538520],[37989756,18924024,80136],[4538520,80136]],[[0,0,0],[0,0,0],[0,0]],[[50516676,186779712,6629448],[186779712,26622288,11760],[6629448,11760]],[[0,0,0],[0,0,0],[0,0]],[[1071427140,478534644,5603472],[478534644,21878640,168],[5603472,168]],[[0,0,0],[0,0],[0]],[[4807543860,766958556,2834412],[766958556,10825416],[2834412]],[[0,0,0],[0,0],[0]],[[12407231256,827212344,846888],[827212344,3178392],[846888]],[[0,0,0],[0,0],[0]],[[21646191504,621013596,138852],[621013596,514248],[138852]],[[0,0,0],[0,0],[0]],[[27239485392,328623540,9996],[328623540,36792],[9996]],[[0,0,0],[0,0],[0]],[[25549343904,122162544,84],[122162544,336],[84]],[[0,0],[0]],[[18172943880,31251780],[31251780]],[[0,0],[0]],[[9876321336,5254452],[5254452]],[[0,0],[0]],[[4100106948,527604],[527604]],[[0,0],[0]],[[1290072756,25032],[25032]],[[0,0],[0]],[[302425704,168],[168]],[[0]],[[51233280]],[[0]],[[5945772]],[[0]],[[427308]],[[0]],[[15036]],[[0]],[[84]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
