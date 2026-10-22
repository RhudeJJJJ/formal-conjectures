/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00326 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 71955138730404112395347060326400000000000 42848849857471901349660504179414981935104 183082075192961695113696772096000000000000))
theorem leaf00326_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 71955138730404112395347060326400000000000 42848849857471901349660504179414981935104 183082075192961695113696772096000000000000 raw00326=true := by decide +kernel
#print axioms leaf00326_raw
theorem leaf00326_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00326=true := by decide +kernel
#print axioms leaf00326_rectangular
def affine00326 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00326 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(49/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00326_transform : affine00326=(NestedInteger.clearedAll 3 raw00326 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(49/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00326_transform
theorem leaf00326_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00326=true := by decide +kernel
#print axioms leaf00326_sign
theorem leaf00326_log : RationalLog.accepts (1036280595/2147483648) (-391195737/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00326_log
def leaf00326 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (234041753199/1000000000000) (1036280595/2147483648) (-391195737/1073741824) 2 8 ![60,0,4] ![(49/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00326
theorem leaf00326_checked : FastNestedCellData.accepts 1 2 4 leaf00326=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (234041753199/1000000000000) (1036280595/2147483648) (-391195737/1073741824) 2 8 ![60,0,4] ![(49/6400),0,(1/16)] ![(1/6400),1,(1/16)] 71955138730404112395347060326400000000000 42848849857471901349660504179414981935104 183082075192961695113696772096000000000000 raw00326 affine00326
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00326_raw leaf00326_rectangular
    leaf00326_transform leaf00326_sign leaf00326_log
#print axioms leaf00326_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
