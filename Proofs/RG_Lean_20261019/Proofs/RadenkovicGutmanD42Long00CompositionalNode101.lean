/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode051
import Proofs.RadenkovicGutmanD42Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1764]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,42336],[0,42336,84]],[[0,0,0],[0,0,0],[0,0]],[[-142884,95256,238140],[95256,954072,132048],[238140,132048]],[[0,0,0],[0,0,0],[0,0]],[[-755244,6395760,1435644],[6395760,5755680,138096],[1435644,138096]],[[0,0,0],[0,0,0],[0,0]],[[34961220,52603992,3592512],[52603992,14414568,56616],[3592512,56616]],[[0,0,0],[0,0,0],[0,0]],[[417138876,201102552,4869144],[201102552,19553520,8400],[4869144,8400]],[[0,0,0],[0,0,0],[0,0]],[[2199389220,455413392,3907512],[455413392,15704640,168],[3907512,168]],[[0,0,0],[0,0],[0]],[[7024631124,675093552,1905456],[675093552,7663824],[1905456]],[[0,0,0],[0,0],[0]],[[15237882408,688450056,555744],[688450056,2236584],[555744]],[[0,0,0],[0,0],[0]],[[23792911464,495040728,90216],[495040728,363216],[90216]],[[0,0,0],[0,0],[0]],[[27651289512,253125096,6636],[253125096,26712],[6636]],[[0,0,0],[0,0],[0]],[[24396482208,91536312,84],[91536312,336],[84]],[[0,0],[0]],[[16519700400,22914360],[22914360]],[[0,0],[0]],[[8619330720,3793776],[3793776]],[[0,0],[0]],[[3457401108,378672],[378672]],[[0,0],[0]],[[1056527220,18312],[18312]],[[0,0],[0]],[[241623144,168],[168]],[[0]],[[40105800]],[[0]],[[4583460]],[[0]],[[327012]],[[0]],[[11676]],[[0]],[[84]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
