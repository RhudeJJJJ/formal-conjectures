/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00331 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 750554403999665210866540740608000000000000 413324910397621460038863463669056367755264 846540770480605077628616966144000000000000))
theorem leaf00331_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 750554403999665210866540740608000000000000 413324910397621460038863463669056367755264 846540770480605077628616966144000000000000 raw00331=true := by decide +kernel
#print axioms leaf00331_raw
theorem leaf00331_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00331=true := by decide +kernel
#print axioms leaf00331_rectangular
def affine00331 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00331 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00331_transform : affine00331=(NestedInteger.clearedAll 3 raw00331 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00331_transform
theorem leaf00331_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00331=true := by decide +kernel
#print axioms leaf00331_sign
theorem leaf00331_log : RationalLog.accepts (794626239/2147483648) (-533746435/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00331_log
def leaf00331 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (488251629231/1000000000000) (794626239/2147483648) (-533746435/1073741824) 2 8 ![52,0,4] ![(19/160),0,(1/4)] ![(1/160),1,(1/4)] affine00331
theorem leaf00331_checked : FastNestedCellData.accepts 1 0 4 leaf00331=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (488251629231/1000000000000) (794626239/2147483648) (-533746435/1073741824) 2 8 ![52,0,4] ![(19/160),0,(1/4)] ![(1/160),1,(1/4)] 750554403999665210866540740608000000000000 413324910397621460038863463669056367755264 846540770480605077628616966144000000000000 raw00331 affine00331
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00331_raw leaf00331_rectangular
    leaf00331_transform leaf00331_sign leaf00331_log
#print axioms leaf00331_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
