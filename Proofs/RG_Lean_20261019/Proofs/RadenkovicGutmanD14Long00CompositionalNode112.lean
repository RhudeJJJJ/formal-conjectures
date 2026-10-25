/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode110
import Proofs.RadenkovicGutmanD14Long00CompositionalNode111
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .plus e110 e111
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,196]],[[0,0],[0,0,0],[0,0,0]],[[0,0,1764],[0,0,3864],[1764,3864,632]],[[0,0,0],[0,0,0],[0,0,0]],[[15876,34776,41244],[34776,75888,22576],[41244,22576,4]],[[0,0,0],[0,0,0],[0,0]],[[693792,899208,273148],[899208,642792,42280],[273148,42280]],[[0,0,0],[0,0,0],[0,0]],[[11336976,7552368,841020],[7552368,2183072,33712],[841020,33712]],[[0,0,0],[0,0,0],[0,0]],[[92823816,32511448,1440576],[32511448,3994696,11576],[1440576,11576]],[[0,0,0],[0,0,0],[0,0]],[[455054272,85206000,1489056],[85206000,4385712,1440],[1489056,1440]],[[0,0,0],[0,0,0],[0,0]],[[1480124832,148104312,961988],[148104312,3012000,8],[961988,8]],[[0,0,0],[0,0],[0]],[[3400503948,179018840,390016],[179018840,1299664],[390016]],[[0,0,0],[0,0],[0]],[[5744009896,154487464,96372],[154487464,341896],[96372]],[[0,0,0],[0,0],[0]],[[7324426744,96369096,13316],[96369096,50272],[13316]],[[0,0,0],[0,0],[0]],[[7173175592,43503176,808],[43503176,3240],[808]],[[0,0,0],[0,0],[0]],[[5452861408,14063728,4],[14063728,16],[4]],[[0,0],[0]],[[3234127384,3173688],[3173688]],[[0,0],[0]],[[1496916180,475440],[475440]],[[0,0],[0]],[[537989840,42744],[42744]],[[0,0],[0]],[[148460364,1800],[1800]],[[0,0],[0]],[[30842904,8],[8]],[[0]],[[4668780]],[[0]],[[487048]],[[0]],[[31544]],[[0]],[[992]],[[0]],[[4]]]
theorem step112 : p112=NestedHorner.add p110 p111 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_plus e112 e110 e111 p110 p111 p112 rfl h110 h111 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
