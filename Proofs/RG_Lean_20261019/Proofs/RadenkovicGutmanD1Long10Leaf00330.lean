/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00330 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 126826645929671778088682048716800000000000 39590686676728838325388851525953733525504 57584055738020370432786222284800000000000))
theorem leaf00330_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 126826645929671778088682048716800000000000 39590686676728838325388851525953733525504 57584055738020370432786222284800000000000 raw00330=true := by decide +kernel
#print axioms leaf00330_raw
theorem leaf00330_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00330=true := by decide +kernel
#print axioms leaf00330_rectangular
def affine00330 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00330 (IntegerComputedClassCell.leftNumerator ![(19/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/160),0,0] ![(1/160),1,(1/4)]))
theorem leaf00330_transform : affine00330=(NestedInteger.clearedAll 3 raw00330 (IntegerComputedClassCell.leftNumerator ![(19/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/160),0,0] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00330_transform
theorem leaf00330_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00330=true := by decide +kernel
#print axioms leaf00330_sign
theorem leaf00330_log : RationalLog.accepts (794495131/4294967296) (-3623862361/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00330_log
def leaf00330 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (68752862523/100000000000) (794495131/4294967296) (-3623862361/4294967296) 3 8 ![52,0,4] ![(19/160),0,0] ![(1/160),1,(1/4)] affine00330
theorem leaf00330_checked : FastNestedCellData.accepts 1 0 4 leaf00330=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (68752862523/100000000000) (794495131/4294967296) (-3623862361/4294967296) 3 8 ![52,0,4] ![(19/160),0,0] ![(1/160),1,(1/4)] 126826645929671778088682048716800000000000 39590686676728838325388851525953733525504 57584055738020370432786222284800000000000 raw00330 affine00330
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00330_raw leaf00330_rectangular
    leaf00330_transform leaf00330_sign leaf00330_log
#print axioms leaf00330_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
