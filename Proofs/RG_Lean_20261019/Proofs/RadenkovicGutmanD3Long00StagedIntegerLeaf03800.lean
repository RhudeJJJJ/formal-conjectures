/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedIntegerLeaf03800Raw
import Proofs.RadenkovicGutmanD3Long00StagedIntegerLeaf03800Affine
import Proofs.RadenkovicGutmanD3Long00StagedIntegerLeaf03800Sign
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedIntegerLeaf03800
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def cell : FastNestedCellData.Cell := LiteralIntegerCell.make FixedDegree03Long00StagedNormPack.pack true (1989/1000000000000) (1180598372542645899845/1180591620717411303424) (3375902963881781/1180591620717411303424) 0 32 ![88,4,4] ![(1/1024),0,0] ![(1/4096),(1/2),(1/2)] affine
theorem checked : FastNestedCellData.accepts 3 4 4 cell=true :=
  IntegerNormProgramPack.accepts_make FixedDegree03Long00StagedIntegerNorm.pack true (1989/1000000000000) (1180598372542645899845/1180591620717411303424) (3375902963881781/1180591620717411303424) 0 32 ![88,4,4] ![(1/1024),0,0] ![(1/4096),(1/2),(1/2)]
    554452277498467617856431795553719887942438092800000000000 554455449524071857599710726616203862780889303008805912576 278760909765747540271347776076522806827998644046659584000000000000 raw affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    raw_checked rectangular_checked affine_checked sign_checked (by decide +kernel)
#print axioms checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedIntegerLeaf03800
