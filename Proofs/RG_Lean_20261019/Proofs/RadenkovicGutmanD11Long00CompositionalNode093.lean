/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode033
import Proofs.RadenkovicGutmanD11Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,121]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,2904],[0,2904,22]],[[0,0,0],[0,0,0],[0,0]],[[-9801,-6534,16335],[-6534,63162,9350],[16335,9350]],[[0,0,0],[0,0,0],[0,0]],[[-269676,248292,99792],[248292,380292,10252],[99792,10252]],[[0,0,0],[0,0,0],[0,0]],[[-1171071,2454012,253440],[2454012,949630,4598],[253440,4598]],[[0,0,0],[0,0,0],[0,0]],[[2713722,9887482,349778],[9887482,1288276,836],[349778,836]],[[0,0,0],[0,0,0],[0,0]],[[39961229,22959420,287518],[22959420,1042624,44],[287518,44]],[[0,0,0],[0,0],[0]],[[167114508,34668172,145090],[34668172,519860],[145090]],[[0,0,0],[0,0],[0]],[[415321082,36034592,44616],[36034592,158862],[44616]],[[0,0,0],[0,0],[0]],[[709035360,26517898,7942],[26517898,28380],[7942]],[[0,0,0],[0,0],[0]],[[882996466,13968086,715],[13968086,2618],[715]],[[0,0,0],[0,0],[0]],[[827161236,5253666,22],[5253666,88],[22]],[[0,0],[0]],[[592397344,1388200],[1388200]],[[0,0],[0]],[[326712408,248820],[248820]],[[0,0],[0]],[[138794601,28292],[28292]],[[0,0],[0]],[[45133572,1782],[1782]],[[0,0],[0]],[[11079618,44],[44]],[[0]],[[2004376]],[[0]],[[256729]],[[0]],[[21736]],[[0]],[[1067]],[[0]],[[22]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
