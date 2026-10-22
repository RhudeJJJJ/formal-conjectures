/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00270 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 126560633340581659840427012915200000000000 11130893435931964357690565239579604942848 16223744864788999331547342438400000000000))
theorem leaf00270_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 126560633340581659840427012915200000000000 11130893435931964357690565239579604942848 16223744864788999331547342438400000000000 raw00270=true := by decide +kernel
#print axioms leaf00270_raw
theorem leaf00270_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00270=true := by decide +kernel
#print axioms leaf00270_rectangular
def affine00270 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00270 (IntegerComputedClassCell.leftNumerator ![(19/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/320),0,0] ![(1/640),1,(1/4)]))
theorem leaf00270_transform : affine00270=(NestedInteger.clearedAll 3 raw00270 (IntegerComputedClassCell.leftNumerator ![(19/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/320),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00270_transform
theorem leaf00270_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00270=true := by decide +kernel
#print axioms leaf00270_sign
theorem leaf00270_log : RationalLog.accepts (112016341/2147483648) (-3171197005/2147483648) 5 8=true := by decide +kernel
#print axioms leaf00270_log
def leaf00270 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (137217313619/200000000000) (112016341/2147483648) (-3171197005/2147483648) 5 8 ![52,0,4] ![(19/320),0,0] ![(1/640),1,(1/4)] affine00270
theorem leaf00270_checked : FastNestedCellData.accepts 1 0 4 leaf00270=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (137217313619/200000000000) (112016341/2147483648) (-3171197005/2147483648) 5 8 ![52,0,4] ![(19/320),0,0] ![(1/640),1,(1/4)] 126560633340581659840427012915200000000000 11130893435931964357690565239579604942848 16223744864788999331547342438400000000000 raw00270 affine00270
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00270_raw leaf00270_rectangular
    leaf00270_transform leaf00270_sign leaf00270_log
#print axioms leaf00270_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
