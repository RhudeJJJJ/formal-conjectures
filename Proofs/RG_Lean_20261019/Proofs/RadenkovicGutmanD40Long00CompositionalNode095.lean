/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode093
import Proofs.RadenkovicGutmanD40Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1600]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-14400],[0,-28800,47520],[-14400,47520,80]],[[0,0,0],[0,0,0],[0,0]],[[-129600,-479520,173280],[-479520,913920,159360],[173280,159360]],[[0,0,0],[0,0,0],[0,0]],[[-5959440,1252800,1453040],[1252800,6410560,174080],[1453040,174080]],[[0,0,0],[0,0,0],[0,0]],[[-31881600,34115040,4114240],[34115040,17074560,72800],[4114240,72800]],[[0,0,0],[0,0,0],[0,0]],[[38569200,167830080,6011040],[167830080,23999360,10720],[6011040,10720]],[[0,0,0],[0,0,0],[0,0]],[[933341120,429830720,5082240],[429830720,19708160,160],[5082240,160]],[[0,0,0],[0,0],[0]],[[4230859760,688489920,2571840],[688489920,9746560],[2571840]],[[0,0,0],[0,0],[0]],[[10953082880,742100000,768960],[742100000,2861440],[768960]],[[0,0,0],[0,0],[0]],[[19132049760,556775200,126240],[556775200,463360],[126240]],[[0,0,0],[0,0],[0]],[[24086497920,294475040,9120],[294475040,33280],[9120]],[[0,0,0],[0,0],[0]],[[22594782720,109426400,80],[109426400,320],[80]],[[0,0],[0]],[[16071192320,27989600],[27989600]],[[0,0],[0]],[[8733669760,4707360],[4707360]],[[0,0],[0]],[[3625670080,473280],[473280]],[[0,0],[0]],[[1140871280,22560],[22560]],[[0,0],[0]],[[267509760,160],[160]],[[0]],[[45341280]],[[0]],[[5267520]],[[0]],[[379440]],[[0]],[[13440]],[[0]],[[80]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
