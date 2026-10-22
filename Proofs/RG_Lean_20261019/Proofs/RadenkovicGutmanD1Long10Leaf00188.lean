/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00188 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 474130290346630703613338451968000000000000 378764105012707217700922571101138638077952 3684095201114959926753132281856000000000000))
theorem leaf00188_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 474130290346630703613338451968000000000000 378764105012707217700922571101138638077952 3684095201114959926753132281856000000000000 raw00188=true := by decide +kernel
#print axioms leaf00188_raw
theorem leaf00188_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00188=true := by decide +kernel
#print axioms leaf00188_rectangular
def affine00188 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00188 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00188_transform : affine00188=(NestedInteger.clearedAll 3 raw00188 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00188_transform
theorem leaf00188_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00188=true := by decide +kernel
#print axioms leaf00188_sign
theorem leaf00188_log : RationalLog.accepts (1555607541/2147483648) (-346207227/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00188_log
def leaf00188 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (102810618167/1000000000000) (1555607541/2147483648) (-346207227/2147483648) 1 8 ![52,0,4] ![(91/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00188
theorem leaf00188_checked : FastNestedCellData.accepts 1 0 4 leaf00188=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (102810618167/1000000000000) (1555607541/2147483648) (-346207227/2147483648) 1 8 ![52,0,4] ![(91/3200),0,(1/2)] ![(3/3200),1,(1/2)] 474130290346630703613338451968000000000000 378764105012707217700922571101138638077952 3684095201114959926753132281856000000000000 raw00188 affine00188
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00188_raw leaf00188_rectangular
    leaf00188_transform leaf00188_sign leaf00188_log
#print axioms leaf00188_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
