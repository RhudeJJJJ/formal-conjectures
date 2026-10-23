/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseStageAffine
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf01753_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] affine01753=true := by decide +kernel
#print axioms leaf01753_sign
theorem leaf01753_log : RationalLog.accepts (536871935/536870912) (4091/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01753_log
def leaf01753 : FastNestedCellData.Cell := IntegerScaledCell.make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] 168684840550400000000000 ![1024,1,1] affine01753
theorem leaf01753_checked : FastNestedCellData.accepts 1 4 4 leaf01753=true :=
  IntegerScaledCell.accepts_make DegreeOneIntegerNorm00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] 168684840550400000000000 168685162242004389465867 107374387168685161977000000000000 ![1,0,0] ![1,1,1] ![1024,1,1] raw01753 inner01753 affine01753
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf01753_raw leaf01753_rectangular leaf01753_inner leaf01753_outer leaf01753_sign leaf01753_log
#print axioms leaf01753_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
