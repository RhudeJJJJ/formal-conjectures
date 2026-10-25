/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode043
import Proofs.RadenkovicGutmanD20Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,3600],[0,7200,-4320],[3600,-4320,1296]],[[0,0,0],[0,0,0],[0,0]],[[0,123120,-7680],[123120,-89232,4608],[-7680,4608]],[[0,0,0],[0,0,0],[0,0]],[[850176,369792,-61184],[369792,-423040,39168],[-61184,39168]],[[0,0,0],[0,0,0],[0,0]],[[5059152,-1202256,-8608],[-1202256,-286352,46944],[-8608,46944]],[[0,0,0],[0,0,0],[0,0]],[[-2025648,-7255056,347232],[-7255056,1231584,19296],[347232,19296]],[[0,0,0],[0,0,0],[0,0]],[[-108048144,-11558384,739360],[-11558384,2949248,2592],[739360,2592]],[[0,0,0],[0,0],[0]],[[-464405824,1067872,721296],[1067872,2928384],[721296]],[[0,0,0],[0,0],[0]],[[-1059957280,30951200,388640],[30951200,1578352],[388640]],[[0,0,0],[0,0],[0]],[[-1506075648,53833776,118768],[53833776,480320],[118768]],[[0,0,0],[0,0],[0]],[[-1329622352,50865392,19296],[50865392,77616],[19296]],[[0,0,0],[0,0],[0]],[[-565594208,30773520,1296],[30773520,5184],[1296]],[[0,0],[0]],[[219699520,12440720],[12440720]],[[0,0],[0]],[[556821920,3354400],[3354400]],[[0,0],[0]],[[470129232,580240],[580240]],[[0,0],[0]],[[249511296,58320],[58320]],[[0,0],[0]],[[91953696,2592],[2592]],[[0]],[[24021760]],[[0]],[[4386320]],[[0]],[[534048]],[[0]],[[39024]],[[0]],[[1296]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
