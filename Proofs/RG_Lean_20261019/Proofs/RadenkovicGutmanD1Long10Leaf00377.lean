/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00377 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 76768724831726719415849530163200000000000 79053174191481627925412100782630457311232 237445925362363869577768599552000000000000))
theorem leaf00377_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 76768724831726719415849530163200000000000 79053174191481627925412100782630457311232 237445925362363869577768599552000000000000 raw00377=true := by decide +kernel
#print axioms leaf00377_raw
theorem leaf00377_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00377=true := by decide +kernel
#print axioms leaf00377_rectangular
def affine00377 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00377 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/2)] ![(3/80),1,(1/2)]))
theorem leaf00377_transform : affine00377=(NestedInteger.clearedAll 3 raw00377 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/2)] ![(3/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00377_transform
theorem leaf00377_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00377=true := by decide +kernel
#print axioms leaf00377_sign
theorem leaf00377_log : RationalLog.accepts (1659040905/2147483648) (-554173423/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00377_log
def leaf00377 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (166465636483/500000000000) (1659040905/2147483648) (-554173423/4294967296) 1 8 ![52,0,4] ![(7/20),0,(1/2)] ![(3/80),1,(1/2)] affine00377
theorem leaf00377_checked : FastNestedCellData.accepts 1 0 4 leaf00377=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (166465636483/500000000000) (1659040905/2147483648) (-554173423/4294967296) 1 8 ![52,0,4] ![(7/20),0,(1/2)] ![(3/80),1,(1/2)] 76768724831726719415849530163200000000000 79053174191481627925412100782630457311232 237445925362363869577768599552000000000000 raw00377 affine00377
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00377_raw leaf00377_rectangular
    leaf00377_transform leaf00377_sign leaf00377_log
#print axioms leaf00377_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
