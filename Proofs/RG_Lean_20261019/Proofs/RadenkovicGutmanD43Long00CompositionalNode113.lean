/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1849]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-33282,33282],[0,33282]],[[0,0,0],[0,0,0],[0,0]],[[149769,-299538,149769],[-299538,310632,88752],[149769,88752]],[[0,0,0],[0,0,0],[0,0]],[[-99846,-698922,798768],[-698922,2215102,81356],[798768,81356]],[[0,0,0],[0,0,0],[0,0]],[[-5541453,5092146,1797228],[5092146,5495228,29584],[1797228,29584]],[[0,0,0],[0,0,0],[0,0]],[[-15254250,31906344,2218800],[31906344,7233288,3698],[2218800,3698]],[[0,0,0],[0,0],[0]],[[32107885,84421642,1638214],[84421642,5628356],[1638214]],[[0,0,0],[0,0],[0]],[[304648636,135032470,739600],[135032470,2658862],[739600]],[[0,0,0],[0,0],[0]],[[951817126,144392108,199692],[144392108,746996],[199692]],[[0,0,0],[0,0],[0]],[[1830166086,107449088,29584],[107449088,114638],[29584]],[[0,0,0],[0,0],[0]],[[2463208216,56405594,1849],[56405594,7396],[1849]],[[0,0],[0]],[[2442588168,20801250],[20801250]],[[0,0],[0]],[[1827684728,5269650],[5269650]],[[0,0],[0]],[[1042188850,872728],[872728]],[[0,0],[0]],[[453073413,85054],[85054]],[[0,0],[0]],[[148962836,3698],[3698]],[[0]],[[36384622]],[[0]],[[6393842]],[[0]],[[763637]],[[0]],[[55470]],[[0]],[[1849]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
