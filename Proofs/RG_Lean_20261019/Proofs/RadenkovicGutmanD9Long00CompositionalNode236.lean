/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode235
import Proofs.RadenkovicGutmanD9Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e236 : NestedArithmetic.Expr 3 := .times e235 e122
noncomputable def p236 : NestedHorner.Poly 3 := [[[81],[0],[0]],[[0,0],[0,0],[0]],[[2511,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[35721,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[309096,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1818126,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[7696053,162,0],[162,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[24209685,3726,0],[3726,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[57625992,38232,0],[38232,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[104671764,230850,0],[230850,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[145176300,911250,0],[911250,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[152626275,2471067,81],[2471067,243,0],[81,0]],[[0,0,0],[0,0,0],[0,0]],[[119502540,4708449,1215],[4708449,3726,0],[1215,0]],[[0,0,0],[0,0,0],[0,0]],[[67324770,6335334,7614],[6335334,23895,0],[7614,0]],[[0,0,0],[0,0,0],[0,0]],[[25436349,5954391,25839],[5954391,83106,0],[25839,0]],[[0,0,0],[0,0,0],[0,0]],[[5351103,3790314,51516],[3790314,170100,0],[51516,0]],[[0,0,0],[0,0,0],[0,0]],[[113724,1530819,61317],[1530819,208170,81],[61317,81]],[[0,0,0],[0,0,0],[0,0]],[[-207765,338256,42282],[338256,147663,567],[42282,567]],[[0,0,0],[0,0,0],[0,0]],[[-32805,24057,15309],[24057,54918,1296],[15309,1296]],[[0,0,0],[0,0,0],[0,0]],[[0,-2187,2187],[-2187,8019,1053],[2187,1053]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,243],[0,243]]]
theorem step236 : p236=NestedArithmetic.mul p235 p122 := by decide +kernel
#print axioms step236
theorem h236 : NestedArithmetic.compile e236=p236 := StagedExprCompile.compile_times e236 e235 e122 p235 p122 p236 rfl h235 h122 step236
#print axioms h236
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
