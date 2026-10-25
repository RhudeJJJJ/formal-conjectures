/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode033
import Proofs.RadenkovicGutmanD9Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,243],[0,243]],[[0,0,0],[0,0,0],[0,0]],[[0,-2187,2187],[-2187,8019,1053],[2187,1053]],[[0,0,0],[0,0,0],[0,0]],[[-32805,24057,15309],[24057,54918,1296],[15309,1296]],[[0,0,0],[0,0,0],[0,0]],[[-207765,338256,42282],[338256,147663,567],[42282,567]],[[0,0,0],[0,0,0],[0,0]],[[113724,1530819,61317],[1530819,208170,81],[61317,81]],[[0,0,0],[0,0],[0]],[[5351103,3790314,51516],[3790314,170100],[51516]],[[0,0,0],[0,0],[0]],[[25436349,5954391,25839],[5954391,83106],[25839]],[[0,0,0],[0,0],[0]],[[67324770,6335334,7614],[6335334,23895],[7614]],[[0,0,0],[0,0],[0]],[[119502540,4708449,1215],[4708449,3726],[1215]],[[0,0,0],[0,0],[0]],[[152626275,2471067,81],[2471067,243],[81]],[[0,0],[0]],[[145176300,911250],[911250]],[[0,0],[0]],[[104671764,230850],[230850]],[[0,0],[0]],[[57625992,38232],[38232]],[[0,0],[0]],[[24209685,3726],[3726]],[[0,0],[0]],[[7696053,162],[162]],[[0]],[[1818126]],[[0]],[[309096]],[[0]],[[35721]],[[0]],[[2511]],[[0]],[[81]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
