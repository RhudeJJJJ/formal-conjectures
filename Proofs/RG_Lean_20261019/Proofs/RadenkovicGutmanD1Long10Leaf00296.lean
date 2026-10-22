/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00296 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 222736042109552851866580995276800000000000 147365281680715244814715320000932927766528 610231198051283800211343802368000000000000))
theorem leaf00296_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 222736042109552851866580995276800000000000 147365281680715244814715320000932927766528 610231198051283800211343802368000000000000 raw00296=true := by decide +kernel
#print axioms leaf00296_raw
theorem leaf00296_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00296=true := by decide +kernel
#print axioms leaf00296_rectangular
def affine00296 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00296 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00296_transform : affine00296=(NestedInteger.clearedAll 3 raw00296 (IntegerComputedClassCell.leftNumerator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/40),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00296_transform
theorem leaf00296_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00296=true := by decide +kernel
#print axioms leaf00296_sign
theorem leaf00296_log : RationalLog.accepts (2288869335/4294967296) (-337899037/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00296_log
def leaf00296 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (120745450373/500000000000) (2288869335/4294967296) (-337899037/1073741824) 1 8 ![52,0,4] ![(3/40),0,(1/2)] ![(1/320),1,(1/2)] affine00296
theorem leaf00296_checked : FastNestedCellData.accepts 1 0 4 leaf00296=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (120745450373/500000000000) (2288869335/4294967296) (-337899037/1073741824) 1 8 ![52,0,4] ![(3/40),0,(1/2)] ![(1/320),1,(1/2)] 222736042109552851866580995276800000000000 147365281680715244814715320000932927766528 610231198051283800211343802368000000000000 raw00296 affine00296
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00296_raw leaf00296_rectangular
    leaf00296_transform leaf00296_sign leaf00296_log
#print axioms leaf00296_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
