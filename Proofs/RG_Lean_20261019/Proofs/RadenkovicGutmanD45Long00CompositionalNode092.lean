/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode089
import Proofs.RadenkovicGutmanD45Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,12150],[0,12150,-3870]],[[0,0,0],[0,0,0],[0,0]],[[0,0,145800],[0,492075,-16740],[145800,-16740]],[[0,0,0],[0,0,0],[0,0]],[[477495,3993705,770310],[3993705,2291490,-119790],[770310,-119790]],[[0,0,0],[0,0,0],[0,0]],[[34400295,34586190,1532520],[34586190,3446955,-140490],[1532520,-140490]],[[0,0,0],[0,0,0],[0,0]],[[371986830,130320495,1206090],[130320495,187110,-57240],[1206090,-57240]],[[0,0,0],[0,0,0],[0,0]],[[1938001815,278692740,-201870],[278692740,-5302980,-7650],[-201870,-7650]],[[0,0,0],[0,0],[0]],[[6156769185,368420265,-1067130],[368420265,-6799770],[-1067130]],[[0,0,0],[0,0],[0]],[[13177104390,302594670,-810540],[302594670,-4062285],[-810540]],[[0,0,0],[0,0],[0]],[[19993760280,137312370,-292050],[137312370,-1309950],[-292050]],[[0,0,0],[0,0],[0]],[[22074724125,8511840,-52470],[8511840,-220005],[-52470]],[[0,0,0],[0,0],[0]],[[17887565070,-30734505,-3780],[-30734505,-15120],[-3780]],[[0,0],[0]],[[10532999070,-20963790],[-20963790]],[[0,0],[0]],[[4318533720,-7166025],[-7166025]],[[0,0],[0]],[[1063321425,-1425060],[-1425060]],[[0,0],[0]],[[33148485,-157185],[-157185]],[[0,0],[0]],[[-90005130,-7470],[-7470]],[[0]],[[-39729420]],[[0]],[[-9228645]],[[0]],[[-1294515]],[[0]],[[-103905]],[[0]],[[-3690]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
