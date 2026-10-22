/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00922 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 68310991809961722327943086080000000000 27415737217259782388899754781708386304 46271020468216492383409274880000000000))
theorem leaf00922_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 68310991809961722327943086080000000000 27415737217259782388899754781708386304 46271020468216492383409274880000000000 raw00922=true := by decide +kernel
#print axioms leaf00922_raw
theorem leaf00922_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00922=true := by decide +kernel
#print axioms leaf00922_rectangular
def affine00922 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00922 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00922_transform : affine00922=(NestedInteger.clearedAll 3 raw00922 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00922_transform
theorem leaf00922_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00922=true := by decide +kernel
#print axioms leaf00922_sign
theorem leaf00922_log : RationalLog.accepts (541201303/2147483648) (-2959792463/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00922_log
def leaf00922 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2962517029/5000000000) (541201303/2147483648) (-2959792463/4294967296) 2 8 ![60,0,4] ![(5/64),0,(1/8)] ![(1/320),1,(1/8)] affine00922
theorem leaf00922_checked : FastNestedCellData.accepts 1 2 4 leaf00922=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2962517029/5000000000) (541201303/2147483648) (-2959792463/4294967296) 2 8 ![60,0,4] ![(5/64),0,(1/8)] ![(1/320),1,(1/8)] 68310991809961722327943086080000000000 27415737217259782388899754781708386304 46271020468216492383409274880000000000 raw00922 affine00922
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00922_raw leaf00922_rectangular
    leaf00922_transform leaf00922_sign leaf00922_log
#print axioms leaf00922_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
