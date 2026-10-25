/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001AffineLength
import Proofs.RadenkovicGutmanPowerBernstein
namespace Gebendorfer.RadenkovicGutman.D2PowerParameterGroup0001
open D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf00005_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf00005_w_affine=true :=
  PowerBernstein.checked 3 ![88,4,4] leaf00005_w_affine
    (by decide +kernel) (by decide +kernel)
#print axioms leaf00005_sign
theorem leaf00005_log : RationalLog.accepts (5496588934861343/4722366482869645213696) (-32262482689769536689873/4722366482869645213696) 20 32=true := by decide +kernel
#print axioms leaf00005_log
noncomputable def leaf00005 : FastNestedCellData.Cell := IntegerScaledCell.make FixedDegree02Long00CompositionalNormPack.pack false (1553815193/125000000000) (5496588934861343/4722366482869645213696) (-32262482689769536689873/4722366482869645213696) 20 32 ![88,4,4] ![(33/32000),0,0] ![(1/32000),1,1] 917210598499603621445072060416000000000000 ![32000,1,1] leaf00005_w_affine
theorem leaf00005_checked : FastNestedCellData.accepts 2 4 4 leaf00005=true :=
  IntegerPiecewiseCell.accepts_make FixedDegree02Long00CompositionalIntegerNorm.pack false (1553815193/125000000000) (5496588934861343/4722366482869645213696) (-32262482689769536689873/4722366482869645213696) 20 32 ![88,4,4] ![(33/32000),0,0] ![(1/32000),1,1]
    917210598499603621445072060416000000000000 1080856068203243453805414415813535407 86951787531791389637723024875000000000 ![33,0,0] ![1,1,1] ![32000,1,1] leaf00005_w_raw leaf00005_w_inner leaf00005_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf00005_raw leaf00005_rectangular leaf00005_inner leaf00005_w_affine_eval leaf00005_sign leaf00005_log
#print axioms leaf00005_checked
end Gebendorfer.RadenkovicGutman.D2PowerParameterGroup0001
