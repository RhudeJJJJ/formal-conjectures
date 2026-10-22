/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00459 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 2356863874052202266567376896000000000000 2461553168064904343116573267928750751744 1204133006339373297639163428864000000000000))
theorem leaf00459_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 2356863874052202266567376896000000000000 2461553168064904343116573267928750751744 1204133006339373297639163428864000000000000 raw00459=true := by decide +kernel
#print axioms leaf00459_raw
theorem leaf00459_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00459=true := by decide +kernel
#print axioms leaf00459_rectangular
def affine00459 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00459 (IntegerComputedClassCell.leftNumerator ![(5/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/32),0,0] ![(1/64),1,(1/2)]))
theorem leaf00459_transform : affine00459=(NestedInteger.clearedAll 3 raw00459 (IntegerComputedClassCell.leftNumerator ![(5/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/32),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00459_transform
theorem leaf00459_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00459=true := by decide +kernel
#print axioms leaf00459_sign
theorem leaf00459_log : RationalLog.accepts (2238296857/2147483648) (44472759/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00459_log
def leaf00459 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1022126773/500000000000) (2238296857/2147483648) (44472759/2147483648) 0 8 ![52,0,4] ![(5/32),0,0] ![(1/64),1,(1/2)] affine00459
theorem leaf00459_checked : FastNestedCellData.accepts 1 0 4 leaf00459=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1022126773/500000000000) (2238296857/2147483648) (44472759/2147483648) 0 8 ![52,0,4] ![(5/32),0,0] ![(1/64),1,(1/2)] 2356863874052202266567376896000000000000 2461553168064904343116573267928750751744 1204133006339373297639163428864000000000000 raw00459 affine00459
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00459_raw leaf00459_rectangular
    leaf00459_transform leaf00459_sign leaf00459_log
#print axioms leaf00459_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
