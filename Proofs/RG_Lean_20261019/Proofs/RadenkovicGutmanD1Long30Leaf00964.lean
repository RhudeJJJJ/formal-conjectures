/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00964 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 214161021957465580734958167654400000000000 141718947735150541364383241138027263688704 488278050855576793873291568742400000000000))
theorem leaf00964_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 214161021957465580734958167654400000000000 141718947735150541364383241138027263688704 488278050855576793873291568742400000000000 raw00964=true := by decide +kernel
#print axioms leaf00964_raw
theorem leaf00964_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00964=true := by decide +kernel
#print axioms leaf00964_rectangular
def affine00964 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00964 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00964_transform : affine00964=(NestedInteger.clearedAll 3 raw00964 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00964_transform
theorem leaf00964_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00964=true := by decide +kernel
#print axioms leaf00964_sign
theorem leaf00964_log : RationalLog.accepts (2202805091/4294967296) (-89618837/268435456) 1 8=true := by decide +kernel
#print axioms leaf00964_log
def leaf00964 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (58048461317/200000000000) (2202805091/4294967296) (-89618837/268435456) 1 8 ![60,0,4] ![(33/320),0,(1/2)] ![(1/320),1,(1/2)] affine00964
theorem leaf00964_checked : FastNestedCellData.accepts 1 2 4 leaf00964=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (58048461317/200000000000) (2202805091/4294967296) (-89618837/268435456) 1 8 ![60,0,4] ![(33/320),0,(1/2)] ![(1/320),1,(1/2)] 214161021957465580734958167654400000000000 141718947735150541364383241138027263688704 488278050855576793873291568742400000000000 raw00964 affine00964
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00964_raw leaf00964_rectangular
    leaf00964_transform leaf00964_sign leaf00964_log
#print axioms leaf00964_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
