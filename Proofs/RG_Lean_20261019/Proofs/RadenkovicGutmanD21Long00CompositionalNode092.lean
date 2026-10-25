/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode089
import Proofs.RadenkovicGutmanD21Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2646],[0,2646,-798]],[[0,0,0],[0,0,0],[0,0]],[[0,0,31752],[0,107163,-2772],[31752,-2772]],[[0,0,0],[0,0,0],[0,0]],[[100359,870345,171990],[870345,515970,-23646],[171990,-23646]],[[0,0,0],[0,0,0],[0,0]],[[7439607,7621614,357336],[7621614,845019,-28266],[357336,-28266]],[[0,0,0],[0,0,0],[0,0]],[[81086670,29105055,317898],[29105055,261702,-11592],[317898,-11592]],[[0,0,0],[0,0,0],[0,0]],[[425367495,63363300,26754],[63363300,-872004,-1554],[26754,-1554]],[[0,0,0],[0,0],[0]],[[1361172561,86065497,-178458],[86065497,-1265082],[-178458]],[[0,0,0],[0,0],[0]],[[2937878790,74260494,-151452],[74260494,-784413],[-151452]],[[0,0,0],[0,0],[0]],[[4504681944,38178546,-56658],[38178546,-257502],[-56658]],[[0,0,0],[0,0],[0]],[[5043670317,7642320,-10374],[7642320,-43701],[-10374]],[[0,0,0],[0,0],[0]],[[4170264462,-3809673,-756],[-3809673,-3024],[-756]],[[0,0],[0]],[[2535788766,-3549630],[-3549630]],[[0,0],[0]],[[1103739000,-1313529],[-1313529]],[[0,0],[0]],[[316352673,-270900],[-270900]],[[0,0],[0]],[[41023605,-30513],[-30513]],[[0,0],[0]],[[-9352266,-1470],[-1470]],[[0]],[[-6333516]],[[0]],[[-1630965]],[[0]],[[-239715]],[[0]],[[-19761]],[[0]],[[-714]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
