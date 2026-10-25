/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode071
import Proofs.RadenkovicGutmanD44Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-104544,0],[-104544,-20592,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1753488,-1962576,0],[-1962576,-248952,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-35832456,-15733080,0],[-15733080,-1217216,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-324996408,-71366240,0],[-71366240,-3123384,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1740009744,-204684392,0],[-204684392,-4602928,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6171556776,-393400832,0],[-393400832,-4049408,0],[0,0]],[[0,0,0],[0,0],[0]],[[-15432397288,-524534472,0],[-524534472,-2143328],[0]],[[0,0,0],[0,0],[0]],[[-28270182864,-495365024,0],[-495365024,-666424],[0]],[[0,0,0],[0,0],[0]],[[-38904402416,-334842640,0],[-334842640,-111936],[0]],[[0,0,0],[0,0],[0]],[[-40893825544,-162152496,0],[-162152496,-7832],[0]],[[0,0,0],[0,0],[0]],[[-33174825904,-55693704,0],[-55693704,0],[0]],[[0,0],[0]],[[-20879281808,-13226752],[-13226752]],[[0,0],[0]],[[-10198633808,-2063336],[-2063336]],[[0,0],[0]],[[-3847699768,-190080],[-190080]],[[0,0],[0]],[[-1108820680,-7832],[-7832]],[[0,0],[0]],[[-239278160,0],[0]],[[0]],[[-37393136]],[[0]],[[-3993352]],[[0]],[[-260568]],[[0]],[[-7832]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
