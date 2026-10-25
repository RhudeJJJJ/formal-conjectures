/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0000AffineLength
import Proofs.RadenkovicGutmanPowerBernstein
namespace Gebendorfer.RadenkovicGutman.D3PowerParameterGroup0000
open D3FullParameterGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf00000_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf00000_w_affine=true :=
  PowerBernstein.checked 3 ![88,4,4] leaf00000_w_affine
    (by decide +kernel) (by decide +kernel)
#print axioms leaf00000_sign
theorem leaf00000_log : RationalLog.accepts (161588114498985/295147905179352825856) (-34043390199624400115565/4722366482869645213696) 21 32=true := by decide +kernel
#print axioms leaf00000_log
noncomputable def leaf00000 : FastNestedCellData.Cell := IntegerScaledCell.make FixedDegree03Long00StagedNormPack.pack false (237143197/40000000000) (161588114498985/295147905179352825856) (-34043390199624400115565/4722366482869645213696) 21 32 ![88,4,4] ![(1/1000),0,0] ![(1/32000),1,1] 559938542576676700115808813056000000000 ![32000,1,1] leaf00000_w_affine
theorem leaf00000_checked : FastNestedCellData.accepts 3 4 4 leaf00000=true :=
  IntegerPiecewiseCell.accepts_make FixedDegree03Long00StagedIntegerNorm.pack false (237143197/40000000000) (161588114498985/295147905179352825856) (-34043390199624400115565/4722366482869645213696) 21 32 ![88,4,4] ![(1/1000),0,0] ![(1/32000),1,1]
    559938542576676700115808813056000000000 308373619350145096512854599795773 52014752816231130849240360000000000 ![32,0,0] ![1,1,1] ![32000,1,1] leaf00000_w_raw leaf00000_w_inner leaf00000_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf00000_raw leaf00000_rectangular leaf00000_inner leaf00000_w_affine_eval leaf00000_sign leaf00000_log
#print axioms leaf00000_checked
end Gebendorfer.RadenkovicGutman.D3PowerParameterGroup0000
