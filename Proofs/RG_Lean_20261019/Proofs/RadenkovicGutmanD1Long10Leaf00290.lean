/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00290 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 652442859380045679187669811200000000000 436395843218828897662880638396933341184 1927870559600049056268471500800000000000))
theorem leaf00290_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 652442859380045679187669811200000000000 436395843218828897662880638396933341184 1927870559600049056268471500800000000000 raw00290=true := by decide +kernel
#print axioms leaf00290_raw
theorem leaf00290_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00290=true := by decide +kernel
#print axioms leaf00290_rectangular
def affine00290 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00290 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00290_transform : affine00290=(NestedInteger.clearedAll 3 raw00290 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00290_transform
theorem leaf00290_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00290=true := by decide +kernel
#print axioms leaf00290_sign
theorem leaf00290_log : RationalLog.accepts (585624791/1073741824) (-1301859519/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00290_log
def leaf00290 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (11318079449/50000000000) (585624791/1073741824) (-1301859519/4294967296) 1 8 ![52,0,4] ![(11/160),0,(1/2)] ![(1/320),1,(1/2)] affine00290
theorem leaf00290_checked : FastNestedCellData.accepts 1 0 4 leaf00290=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (11318079449/50000000000) (585624791/1073741824) (-1301859519/4294967296) 1 8 ![52,0,4] ![(11/160),0,(1/2)] ![(1/320),1,(1/2)] 652442859380045679187669811200000000000 436395843218828897662880638396933341184 1927870559600049056268471500800000000000 raw00290 affine00290
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00290_raw leaf00290_rectangular
    leaf00290_transform leaf00290_sign leaf00290_log
#print axioms leaf00290_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
