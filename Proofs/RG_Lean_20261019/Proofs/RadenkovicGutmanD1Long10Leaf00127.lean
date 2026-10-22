/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00127 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2192538162693805229050586726400000000000 1694713700479060371148264435416664375296 14852435278584323619992633344000000000000))
theorem leaf00127_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2192538162693805229050586726400000000000 1694713700479060371148264435416664375296 14852435278584323619992633344000000000000 raw00127=true := by decide +kernel
#print axioms leaf00127_raw
theorem leaf00127_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00127=true := by decide +kernel
#print axioms leaf00127_rectangular
def affine00127 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00127 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00127_transform : affine00127=(NestedInteger.clearedAll 3 raw00127 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00127_transform
theorem leaf00127_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00127=true := by decide +kernel
#print axioms leaf00127_sign
theorem leaf00127_log : RationalLog.accepts (1489887705/2147483648) (-785111487/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00127_log
def leaf00127 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (28525855671/250000000000) (1489887705/2147483648) (-785111487/4294967296) 1 8 ![52,0,4] ![(3/200),0,(1/4)] ![(1/1600),1,(1/4)] affine00127
theorem leaf00127_checked : FastNestedCellData.accepts 1 0 4 leaf00127=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (28525855671/250000000000) (1489887705/2147483648) (-785111487/4294967296) 1 8 ![52,0,4] ![(3/200),0,(1/4)] ![(1/1600),1,(1/4)] 2192538162693805229050586726400000000000 1694713700479060371148264435416664375296 14852435278584323619992633344000000000000 raw00127 affine00127
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00127_raw leaf00127_rectangular
    leaf00127_transform leaf00127_sign leaf00127_log
#print axioms leaf00127_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
