/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode075
import Proofs.RadenkovicGutmanD44Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1936]],[[0,0],[0,0,0],[0,0]],[[0,0,17424],[0,34848,34848],[17424,34848]],[[0,0,0],[0,0,0],[0,0]],[[-156816,574992,307824],[574992,929280,92928],[307824,92928]],[[0,0,0],[0,0,0],[0,0]],[[1986336,9252144,1349392],[9252144,4371488,85184],[1349392,85184]],[[0,0,0],[0,0,0],[0,0]],[[55983312,53300016,2768480],[53300016,9300544,30976],[2768480,30976]],[[0,0,0],[0,0,0],[0,0]],[[431429856,164068256,3182784],[164068256,11011968,3872],[3182784,3872]],[[0,0,0],[0,0],[0]],[[1795134704,314179888,2199296],[314179888,7829184],[2199296]],[[0,0,0],[0,0],[0]],[[4813476800,403321072,931216],[403321072,3411232],[931216]],[[0,0,0],[0,0],[0]],[[9032775840,361218880,236192],[361218880,890560],[236192]],[[0,0,0],[0,0],[0]],[[12424121248,230250416,32912],[230250416,127776],[32912]],[[0,0,0],[0,0],[0]],[[12878601120,105041552,1936],[105041552,7744],[1936]],[[0,0],[0]],[[10229552960,34027136],[34027136]],[[0,0],[0]],[[6281410080,7637520],[7637520]],[[0,0],[0]],[[2989063968,1128688],[1128688]],[[0,0],[0]],[[1098290864,98736],[98736]],[[0,0],[0]],[[308358336,3872],[3872]],[[0]],[[64875360]],[[0]],[[9892960]],[[0]],[[1031888]],[[0]],[[65824]],[[0]],[[1936]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
