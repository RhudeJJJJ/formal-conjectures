/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedIntegerLeaf03800Prepared
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem raw_checked : IntegerNormProgramPack.rawCheck FixedDegree03Long00StagedIntegerNorm.pack true 554452277498467617856431795553719887942438092800000000000 554455449524071857599710726616203862780889303008805912576 278760909765747540271347776076522806827998644046659584000000000000 raw=true := by decide +kernel
theorem rectangular_checked : NestedInteger.rectangular 3 ![88,4,4] raw=true := by decide +kernel
#print axioms raw_checked
#print axioms rectangular_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedIntegerLeaf03800
