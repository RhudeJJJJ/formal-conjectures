/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0001AffineLength
import Proofs.RadenkovicGutmanPowerBernstein
namespace Gebendorfer.RadenkovicGutman.D3PowerParameterGroup0001
open D3FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf00004_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf00004_w_affine=true :=
  PowerBernstein.checked 3 ![88,4,4] leaf00004_w_affine
    (by decide +kernel) (by decide +kernel)
#print axioms leaf00004_sign
theorem leaf00004_log : RationalLog.accepts (2833081764394603/4722366482869645213696) (-8456846672845676703229/1180591620717411303424) 21 32=true := by decide +kernel
#print axioms leaf00004_log
noncomputable def leaf00004 : FastNestedCellData.Cell := IntegerScaledCell.make FixedDegree03Long00StagedNormPack.pack false (1222193447/200000000000) (2833081764394603/4722366482869645213696) (-8456846672845676703229/1180591620717411303424) 21 32 ![88,4,4] ![(33/32000),0,0] ![(1/32000),1,1] 1154329073939143627078833170022400000000000 ![32000,1,1] leaf00004_w_affine
theorem leaf00004_checked : FastNestedCellData.accepts 3 4 4 leaf00004=true :=
  IntegerPiecewiseCell.accepts_make FixedDegree03Long00StagedIntegerNorm.pack false (1222193447/200000000000) (2833081764394603/4722366482869645213696) (-8456846672845676703229/1180591620717411303424) 21 32 ![88,4,4] ![(33/32000),0,0] ![(1/32000),1,1]
    1154329073939143627078833170022400000000000 696746728664192206214242628863056827 114015785369235776341753308200000000000 ![33,0,0] ![1,1,1] ![32000,1,1] leaf00004_w_raw leaf00004_w_inner leaf00004_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf00004_raw leaf00004_rectangular leaf00004_inner leaf00004_w_affine_eval leaf00004_sign leaf00004_log
#print axioms leaf00004_checked
end Gebendorfer.RadenkovicGutman.D3PowerParameterGroup0001
