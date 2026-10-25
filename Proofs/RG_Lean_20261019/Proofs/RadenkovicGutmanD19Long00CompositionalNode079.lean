/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode033
import Proofs.RadenkovicGutmanD19Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1083],[0,1083]],[[0,0,0],[0,0,0],[0,0]],[[0,-9747,9747],[-9747,35739,4693],[9747,4693]],[[0,0,0],[0,0,0],[0,0]],[[-146205,107217,68229],[107217,244758,5776],[68229,5776]],[[0,0,0],[0,0,0],[0,0]],[[-925965,1507536,188442],[1507536,658103,2527],[188442,2527]],[[0,0,0],[0,0,0],[0,0]],[[506844,6822539,273277],[6822539,927770,361],[273277,361]],[[0,0,0],[0,0],[0]],[[23848743,16892634,229596],[16892634,758100],[229596]],[[0,0,0],[0,0],[0]],[[113364469,26537471,115159],[26537471,370386],[115159]],[[0,0,0],[0,0],[0]],[[300052370,28235254,33934],[28235254,106495],[33934]],[[0,0,0],[0,0],[0]],[[532597740,20984569,5415],[20984569,16606],[5415]],[[0,0,0],[0,0],[0]],[[680223275,11013027,361],[11013027,1083],[361]],[[0,0],[0]],[[647020300,4061250],[4061250]],[[0,0],[0]],[[466500084,1028850],[1028850]],[[0,0],[0]],[[256826952,170392],[170392]],[[0,0],[0]],[[107897485,16606],[16606]],[[0,0],[0]],[[34299693,722],[722]],[[0]],[[8103006]],[[0]],[[1377576]],[[0]],[[159201]],[[0]],[[11191]],[[0]],[[361]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
