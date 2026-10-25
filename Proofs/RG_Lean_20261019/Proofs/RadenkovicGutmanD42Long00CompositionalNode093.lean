/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode033
import Proofs.RadenkovicGutmanD42Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1764]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,42336],[0,42336,84]],[[0,0,0],[0,0,0],[0,0]],[[-142884,-95256,238140],[-95256,920808,132048],[238140,132048]],[[0,0,0],[0,0,0],[0,0]],[[-3912300,3619728,1435644],[3619728,5467392,138096],[1435644,138096]],[[0,0,0],[0,0,0],[0,0]],[[-16740108,35430696,3592512],[35430696,13435128,56616],[3592512,56616]],[[0,0,0],[0,0,0],[0,0]],[[40578300,141383592,4869144],[141383592,17860752,8400],[4869144,8400]],[[0,0,0],[0,0,0],[0,0]],[[577746036,324819936,3907512],[324819936,14063616,168],[3907512,168]],[[0,0,0],[0,0],[0]],[[2390255700,484445808,1905456],[484445808,6739824],[1905456]],[[0,0,0],[0,0],[0]],[[5884863432,496120968,555744],[496120968,1937208],[555744]],[[0,0,0],[0,0],[0]],[[9948548904,358434216,90216],[358434216,311472],[90216]],[[0,0,0],[0,0],[0]],[[12254677176,184394616,6636],[184394616,23016],[6636]],[[0,0,0],[0,0],[0]],[[11335765056,67204872,84],[67204872,336],[84]],[[0,0],[0]],[[7998024048,16992360],[16992360]],[[0,0],[0]],[[4331864544,2850960],[2850960]],[[0,0],[0]],[[1799446404,290304],[290304]],[[0,0],[0]],[[568670004,14616],[14616]],[[0,0],[0]],[[134446536,168],[168]],[[0]],[[23094792]],[[0]],[[2741844]],[[0]],[[205380]],[[0]],[[7980]],[[0]],[[84]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
