/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00132 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 64807678951537448599851263590400000000000 284170408119425276874713899121107795968 808857665743678846268551987200000000000))
theorem leaf00132_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 64807678951537448599851263590400000000000 284170408119425276874713899121107795968 808857665743678846268551987200000000000 raw00132=true := by decide +kernel
#print axioms leaf00132_raw
theorem leaf00132_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00132=true := by decide +kernel
#print axioms leaf00132_rectangular
def affine00132 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00132 (IntegerComputedClassCell.leftNumerator ![(13/800),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/800),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00132_transform : affine00132=(NestedInteger.clearedAll 3 raw00132 (IntegerComputedClassCell.leftNumerator ![(13/800),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/800),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00132_transform
theorem leaf00132_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00132=true := by decide +kernel
#print axioms leaf00132_sign
theorem leaf00132_log : RationalLog.accepts (6968239/2147483648) (-1538320289/536870912) 9 8=true := by decide +kernel
#print axioms leaf00132_log
def leaf00132 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (70264626313/200000000000) (6968239/2147483648) (-1538320289/536870912) 9 8 ![52,0,4] ![(13/800),0,0] ![(1/1600),1,(1/4)] affine00132
theorem leaf00132_checked : FastNestedCellData.accepts 1 0 4 leaf00132=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (70264626313/200000000000) (6968239/2147483648) (-1538320289/536870912) 9 8 ![52,0,4] ![(13/800),0,0] ![(1/1600),1,(1/4)] 64807678951537448599851263590400000000000 284170408119425276874713899121107795968 808857665743678846268551987200000000000 raw00132 affine00132
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00132_raw leaf00132_rectangular
    leaf00132_transform leaf00132_sign leaf00132_log
#print axioms leaf00132_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
