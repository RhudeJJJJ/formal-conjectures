/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00888 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1727846903050774064749617348608000000000000 916096317293293692211752033637285415092224 2445094279206608176673206566912000000000000))
theorem leaf00888_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1727846903050774064749617348608000000000000 916096317293293692211752033637285415092224 2445094279206608176673206566912000000000000 raw00888=true := by decide +kernel
#print axioms leaf00888_raw
theorem leaf00888_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00888=true := by decide +kernel
#print axioms leaf00888_rectangular
def affine00888 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00888 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00888_transform : affine00888=(NestedInteger.clearedAll 3 raw00888 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00888_transform
theorem leaf00888_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00888=true := by decide +kernel
#print axioms leaf00888_sign
theorem leaf00888_log : RationalLog.accepts (1656525819/4294967296) (-511488431/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00888_log
def leaf00888 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (187333536601/500000000000) (1656525819/4294967296) (-511488431/1073741824) 2 8 ![60,0,4] ![(41/640),0,(1/4)] ![(1/640),1,(1/4)] affine00888
theorem leaf00888_checked : FastNestedCellData.accepts 1 2 4 leaf00888=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (187333536601/500000000000) (1656525819/4294967296) (-511488431/1073741824) 2 8 ![60,0,4] ![(41/640),0,(1/4)] ![(1/640),1,(1/4)] 1727846903050774064749617348608000000000000 916096317293293692211752033637285415092224 2445094279206608176673206566912000000000000 raw00888 affine00888
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00888_raw leaf00888_rectangular
    leaf00888_transform leaf00888_sign leaf00888_log
#print axioms leaf00888_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
