/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00958 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1613407439476203645046462873600000000000 879241674651383191702616983949858045952 1963423438589881683516850176000000000000))
theorem leaf00958_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1613407439476203645046462873600000000000 879241674651383191702616983949858045952 1963423438589881683516850176000000000000 raw00958=true := by decide +kernel
#print axioms leaf00958_raw
theorem leaf00958_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00958=true := by decide +kernel
#print axioms leaf00958_rectangular
def affine00958 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00958 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00958_transform : affine00958=(NestedInteger.clearedAll 3 raw00958 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00958_transform
theorem leaf00958_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00958=true := by decide +kernel
#print axioms leaf00958_sign
theorem leaf00958_log : RationalLog.accepts (202079545/536870912) (-65571823/134217728) 2 8=true := by decide +kernel
#print axioms leaf00958_log
def leaf00958 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (111952630463/250000000000) (202079545/536870912) (-65571823/134217728) 2 8 ![60,0,4] ![(1/10),0,(1/4)] ![(1/320),1,(1/4)] affine00958
theorem leaf00958_checked : FastNestedCellData.accepts 1 2 4 leaf00958=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (111952630463/250000000000) (202079545/536870912) (-65571823/134217728) 2 8 ![60,0,4] ![(1/10),0,(1/4)] ![(1/320),1,(1/4)] 1613407439476203645046462873600000000000 879241674651383191702616983949858045952 1963423438589881683516850176000000000000 raw00958 affine00958
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00958_raw leaf00958_rectangular
    leaf00958_transform leaf00958_sign leaf00958_log
#print axioms leaf00958_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
