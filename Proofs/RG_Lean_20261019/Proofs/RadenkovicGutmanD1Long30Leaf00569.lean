/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00569 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 297694494348852865989301239808000000000000 257663205728655764190287282389139161350144 3991547797755233384012628099072000000000000))
theorem leaf00569_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 297694494348852865989301239808000000000000 257663205728655764190287282389139161350144 3991547797755233384012628099072000000000000 raw00569=true := by decide +kernel
#print axioms leaf00569_raw
theorem leaf00569_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00569=true := by decide +kernel
#print axioms leaf00569_rectangular
def affine00569 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00569 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00569_transform : affine00569=(NestedInteger.clearedAll 3 raw00569 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00569_transform
theorem leaf00569_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00569=true := by decide +kernel
#print axioms leaf00569_sign
theorem leaf00569_log : RationalLog.accepts (3492002139/4294967296) (-222230957/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00569_log
def leaf00569 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (32276101751/500000000000) (3492002139/4294967296) (-222230957/2147483648) 1 8 ![60,0,4] ![(7/400),0,(1/2)] ![(1/3200),1,(1/2)] affine00569
theorem leaf00569_checked : FastNestedCellData.accepts 1 2 4 leaf00569=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (32276101751/500000000000) (3492002139/4294967296) (-222230957/2147483648) 1 8 ![60,0,4] ![(7/400),0,(1/2)] ![(1/3200),1,(1/2)] 297694494348852865989301239808000000000000 257663205728655764190287282389139161350144 3991547797755233384012628099072000000000000 raw00569 affine00569
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00569_raw leaf00569_rectangular
    leaf00569_transform leaf00569_sign leaf00569_log
#print axioms leaf00569_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
