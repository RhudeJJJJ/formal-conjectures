/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Integer00Stage01753Affine
namespace Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf01753_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] affine01753=true := by decide +kernel
#print axioms leaf01753_sign
theorem leaf01753_log : RationalLog.accepts (536871935/536870912) (4091/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01753_log
def leaf01753 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] affine01753
theorem leaf01753_checked : FastNestedCellData.accepts 1 4 4 leaf01753=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] 90561984186867829964800000000000 90562156893732861280543209160704 57646185164693100751459713024000000000000 raw01753 affine01753
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01753_raw leaf01753_rectangular
    leaf01753_transform leaf01753_sign leaf01753_log
#print axioms leaf01753_checked
end Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
