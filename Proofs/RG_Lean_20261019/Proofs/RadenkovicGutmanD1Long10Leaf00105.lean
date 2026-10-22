/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00105 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 183643674517412958793052979200000000000 301884064791163418031283122160533504 1184524293820889571734323200000000000))
theorem leaf00105_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 183643674517412958793052979200000000000 301884064791163418031283122160533504 1184524293820889571734323200000000000 raw00105=true := by decide +kernel
#print axioms leaf00105_raw
theorem leaf00105_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00105=true := by decide +kernel
#print axioms leaf00105_rectangular
def affine00105 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00105 (IntegerComputedClassCell.leftNumerator ![(9/800),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/800),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00105_transform : affine00105=(NestedInteger.clearedAll 3 raw00105 (IntegerComputedClassCell.leftNumerator ![(9/800),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/800),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00105_transform
theorem leaf00105_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00105=true := by decide +kernel
#print axioms leaf00105_sign
theorem leaf00105_log : RationalLog.accepts (5626391/4294967296) (-3563604791/1073741824) 10 8=true := by decide +kernel
#print axioms leaf00105_log
def leaf00105 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1592854967/6250000000) (5626391/4294967296) (-3563604791/1073741824) 10 8 ![52,0,4] ![(9/800),0,0] ![(1/3200),1,(1/4)] affine00105
theorem leaf00105_checked : FastNestedCellData.accepts 1 0 4 leaf00105=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1592854967/6250000000) (5626391/4294967296) (-3563604791/1073741824) 10 8 ![52,0,4] ![(9/800),0,0] ![(1/3200),1,(1/4)] 183643674517412958793052979200000000000 301884064791163418031283122160533504 1184524293820889571734323200000000000 raw00105 affine00105
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00105_raw leaf00105_rectangular
    leaf00105_transform leaf00105_sign leaf00105_log
#print axioms leaf00105_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
