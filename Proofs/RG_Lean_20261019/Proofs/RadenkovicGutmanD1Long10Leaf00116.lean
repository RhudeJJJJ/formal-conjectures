/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00116 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 171133806126440575251901736550400000000000 153294092619133737960739522303388647686144 3304755452546193585887722340352000000000000))
theorem leaf00116_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 171133806126440575251901736550400000000000 153294092619133737960739522303388647686144 3304755452546193585887722340352000000000000 raw00116=true := by decide +kernel
#print axioms leaf00116_raw
theorem leaf00116_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00116=true := by decide +kernel
#print axioms leaf00116_rectangular
def affine00116 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00116 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00116_transform : affine00116=(NestedInteger.clearedAll 3 raw00116 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00116_transform
theorem leaf00116_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00116=true := by decide +kernel
#print axioms leaf00116_sign
theorem leaf00116_log : RationalLog.accepts (3676694855/4294967296) (-166891419/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00116_log
def leaf00116 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (46385911097/1000000000000) (3676694855/4294967296) (-166891419/2147483648) 1 8 ![52,0,4] ![(1/80),0,(1/2)] ![(1/1600),1,(1/2)] affine00116
theorem leaf00116_checked : FastNestedCellData.accepts 1 0 4 leaf00116=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (46385911097/1000000000000) (3676694855/4294967296) (-166891419/2147483648) 1 8 ![52,0,4] ![(1/80),0,(1/2)] ![(1/1600),1,(1/2)] 171133806126440575251901736550400000000000 153294092619133737960739522303388647686144 3304755452546193585887722340352000000000000 raw00116 affine00116
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00116_raw leaf00116_rectangular
    leaf00116_transform leaf00116_sign leaf00116_log
#print axioms leaf00116_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
