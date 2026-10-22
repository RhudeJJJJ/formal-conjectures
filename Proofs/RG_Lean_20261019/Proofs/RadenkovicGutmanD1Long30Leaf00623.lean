/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00623 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 244170619676137377718597582848000000000000 173711061502245833357126575489869554909184 1093635363990761927286817030144000000000000))
theorem leaf00623_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 244170619676137377718597582848000000000000 173711061502245833357126575489869554909184 1093635363990761927286817030144000000000000 raw00623=true := by decide +kernel
#print axioms leaf00623_raw
theorem leaf00623_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00623=true := by decide +kernel
#print axioms leaf00623_rectangular
def affine00623 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00623 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00623_transform : affine00623=(NestedInteger.clearedAll 3 raw00623 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00623_transform
theorem leaf00623_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00623=true := by decide +kernel
#print axioms leaf00623_sign
theorem leaf00623_log : RationalLog.accepts (2636763213/4294967296) (-523869883/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00623_log
def leaf00623 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (79419094893/500000000000) (2636763213/4294967296) (-523869883/2147483648) 1 8 ![60,0,4] ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00623
theorem leaf00623_checked : FastNestedCellData.accepts 1 2 4 leaf00623=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (79419094893/500000000000) (2636763213/4294967296) (-523869883/2147483648) 1 8 ![60,0,4] ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)] 244170619676137377718597582848000000000000 173711061502245833357126575489869554909184 1093635363990761927286817030144000000000000 raw00623 affine00623
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00623_raw leaf00623_rectangular
    leaf00623_transform leaf00623_sign leaf00623_log
#print axioms leaf00623_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
