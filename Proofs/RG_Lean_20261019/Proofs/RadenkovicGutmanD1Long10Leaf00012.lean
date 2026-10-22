/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00012 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3543414900486526930039865344000000000000 42515829318343044361062925843038208 864586410354134065610752000000000000))
theorem leaf00012_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3543414900486526930039865344000000000000 42515829318343044361062925843038208 864586410354134065610752000000000000 raw00012=true := by decide +kernel
#print axioms leaf00012_raw
theorem leaf00012_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00012=true := by decide +kernel
#print axioms leaf00012_rectangular
def affine00012 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00012 (IntegerComputedClassCell.leftNumerator ![(1/500),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/500),0,0] ![(3/16000),1,(1/4)]))
theorem leaf00012_transform : affine00012=(NestedInteger.clearedAll 3 raw00012 (IntegerComputedClassCell.leftNumerator ![(1/500),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/500),0,0] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00012_transform
theorem leaf00012_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00012=true := by decide +kernel
#print axioms leaf00012_sign
theorem leaf00012_log : RationalLog.accepts (24559/2147483648) (-24435634917/4294967296) 17 8=true := by decide +kernel
#print axioms leaf00012_log
def leaf00012 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (6146845013/125000000000) (24559/2147483648) (-24435634917/4294967296) 17 8 ![52,0,4] ![(1/500),0,0] ![(3/16000),1,(1/4)] affine00012
theorem leaf00012_checked : FastNestedCellData.accepts 1 0 4 leaf00012=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (6146845013/125000000000) (24559/2147483648) (-24435634917/4294967296) 17 8 ![52,0,4] ![(1/500),0,0] ![(3/16000),1,(1/4)] 3543414900486526930039865344000000000000 42515829318343044361062925843038208 864586410354134065610752000000000000 raw00012 affine00012
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00012_raw leaf00012_rectangular
    leaf00012_transform leaf00012_sign leaf00012_log
#print axioms leaf00012_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
