/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,2025]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-36450,36450],[0,36450]],[[0,0,0],[0,0,0],[0,0]],[[164025,-328050,164025],[-328050,340200,97200],[164025,97200]],[[0,0,0],[0,0,0],[0,0]],[[-109350,-765450,874800],[-765450,2425950,89100],[874800,89100]],[[0,0,0],[0,0,0],[0,0]],[[-6068925,5576850,1968300],[5576850,6018300,32400],[1968300,32400]],[[0,0,0],[0,0,0],[0,0]],[[-16706250,34943400,2430000],[34943400,7921800,4050],[2430000,4050]],[[0,0,0],[0,0],[0]],[[35164125,92457450,1794150],[92457450,6164100],[1794150]],[[0,0,0],[0,0],[0]],[[333647100,147885750,810000],[147885750,2911950],[810000]],[[0,0,0],[0,0],[0]],[[1042417350,158136300,218700],[158136300,818100],[218700]],[[0,0,0],[0,0],[0]],[[2004373350,117676800,32400],[117676800,125550],[32400]],[[0,0,0],[0,0],[0]],[[2697672600,61774650,2025],[61774650,8100],[2025]],[[0,0],[0]],[[2675089800,22781250],[22781250]],[[0,0],[0]],[[2001655800,5771250],[5771250]],[[0,0],[0]],[[1141391250,955800],[955800]],[[0,0],[0]],[[496199925,93150],[93150]],[[0,0],[0]],[[163142100,4050],[4050]],[[0]],[[39847950]],[[0]],[[7002450]],[[0]],[[836325]],[[0]],[[60750]],[[0]],[[2025]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
