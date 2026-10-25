/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,900]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-16200,16200],[0,16200]],[[0,0,0],[0,0,0],[0,0]],[[72900,-145800,72900],[-145800,151200,43200],[72900,43200]],[[0,0,0],[0,0,0],[0,0]],[[-48600,-340200,388800],[-340200,1078200,39600],[388800,39600]],[[0,0,0],[0,0,0],[0,0]],[[-2697300,2478600,874800],[2478600,2674800,14400],[874800,14400]],[[0,0,0],[0,0,0],[0,0]],[[-7425000,15530400,1080000],[15530400,3520800,1800],[1080000,1800]],[[0,0,0],[0,0],[0]],[[15628500,41092200,797400],[41092200,2739600],[797400]],[[0,0,0],[0,0],[0]],[[148287600,65727000,360000],[65727000,1294200],[360000]],[[0,0,0],[0,0],[0]],[[463296600,70282800,97200],[70282800,363600],[97200]],[[0,0,0],[0,0],[0]],[[890832600,52300800,14400],[52300800,55800],[14400]],[[0,0,0],[0,0],[0]],[[1198965600,27455400,900],[27455400,3600],[900]],[[0,0],[0]],[[1188928800,10125000],[10125000]],[[0,0],[0]],[[889624800,2565000],[2565000]],[[0,0],[0]],[[507285000,424800],[424800]],[[0,0],[0]],[[220533300,41400],[41400]],[[0,0],[0]],[[72507600,1800],[1800]],[[0]],[[17710200]],[[0]],[[3112200]],[[0]],[[371700]],[[0]],[[27000]],[[0]],[[900]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
