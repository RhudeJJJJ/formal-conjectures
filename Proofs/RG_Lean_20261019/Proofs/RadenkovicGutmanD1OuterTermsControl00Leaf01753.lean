/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerOuterClassCell
import Proofs.RadenkovicGutmanD1Integer00Stage01753Inner
namespace Gebendorfer.RadenkovicGutman.DegreeOneOuterTermsControl00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneInteger00Stages
def affine01753 : NestedInteger.Poly 3 := rg_integer_data% (IntegerOuterTerms.transform (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1] 0) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1] 0) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1] 0) 0 inner01753)
theorem leaf01753_transform : affine01753=(IntegerOuterTerms.transform (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1] 0) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1] 0) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1] 0) 0 inner01753) := by decide +kernel
#print axioms leaf01753_transform
theorem leaf01753_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] affine01753=true := by decide +kernel
#print axioms leaf01753_sign
theorem leaf01753_log : RationalLog.accepts (536871935/536870912) (4091/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01753_log
def leaf01753 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] affine01753
theorem leaf01753_checked : FastNestedCellData.accepts 1 4 4 leaf01753=true :=
  IntegerOuterClassCell.accepts_make DegreeOneIntegerNorm00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] 90561984186867829964800000000000 90562156893732861280543209160704 57646185164693100751459713024000000000000 raw01753 inner01753 affine01753
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01753_raw leaf01753_rectangular
    leaf01753_inner leaf01753_transform leaf01753_sign leaf01753_log
#print axioms leaf01753_checked
end Gebendorfer.RadenkovicGutman.DegreeOneOuterTermsControl00
