/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00277 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2320015890591318607089236967424000000000000 1206501931874120450829223182865104604495872 3197683896904330633758864572416000000000000))
theorem leaf00277_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2320015890591318607089236967424000000000000 1206501931874120450829223182865104604495872 3197683896904330633758864572416000000000000 raw00277=true := by decide +kernel
#print axioms leaf00277_raw
theorem leaf00277_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00277=true := by decide +kernel
#print axioms leaf00277_rectangular
def affine00277 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00277 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00277_transform : affine00277=(NestedInteger.clearedAll 3 raw00277 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00277_transform
theorem leaf00277_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00277=true := by decide +kernel
#print axioms leaf00277_sign
theorem leaf00277_log : RationalLog.accepts (1621686189/4294967296) (-2091600773/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00277_log
def leaf00277 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (377304940317/1000000000000) (1621686189/4294967296) (-2091600773/4294967296) 2 8 ![52,0,4] ![(1/16),0,(1/4)] ![(1/640),1,(1/4)] affine00277
theorem leaf00277_checked : FastNestedCellData.accepts 1 0 4 leaf00277=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (377304940317/1000000000000) (1621686189/4294967296) (-2091600773/4294967296) 2 8 ![52,0,4] ![(1/16),0,(1/4)] ![(1/640),1,(1/4)] 2320015890591318607089236967424000000000000 1206501931874120450829223182865104604495872 3197683896904330633758864572416000000000000 raw00277 affine00277
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00277_raw leaf00277_rectangular
    leaf00277_transform leaf00277_sign leaf00277_log
#print axioms leaf00277_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
