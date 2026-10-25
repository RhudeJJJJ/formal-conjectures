/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode113
import Proofs.RadenkovicGutmanD34Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1156]],[[0,0],[0,0,0],[0,0]],[[0,0,10404],[0,0,20808],[10404,20808]],[[0,0,0],[0,0,0],[0,0]],[[93636,187272,183804],[187272,374544,55488],[183804,55488]],[[0,0,0],[0,0,0],[0,0]],[[3308472,3807864,805732],[3807864,1997568,50864],[805732,50864]],[[0,0,0],[0,0,0],[0,0]],[[43728012,23783544,1653080],[23783544,4494528,18496],[1653080,18496]],[[0,0,0],[0,0,0],[0,0]],[[285978216,76684416,1900464],[76684416,5548800,2312],[1900464,2312]],[[0,0,0],[0,0],[0]],[[1121482996,151970072,1313216],[151970072,4096864],[1313216]],[[0,0,0],[0,0],[0]],[[2932378960,200855000,556036],[200855000,1849600],[556036]],[[0,0,0],[0,0],[0]],[[5440762552,184724176,141032],[184724176,499392],[141032]],[[0,0,0],[0,0],[0]],[[7445308168,120723392,19652],[120723392,73984],[19652]],[[0,0,0],[0,0],[0]],[[7700476672,56401240,1156],[56401240,4624],[1156]],[[0,0],[0]],[[6110985920,18692520],[18692520]],[[0,0],[0]],[[3751173760,4288760],[4288760]],[[0,0],[0]],[[1784843192,647360],[647360]],[[0,0],[0]],[[655799956,57800],[57800]],[[0,0],[0]],[[184123056,2312],[2312]],[[0]],[[38737560]],[[0]],[[5907160]],[[0]],[[616148]],[[0]],[[39304]],[[0]],[[1156]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
