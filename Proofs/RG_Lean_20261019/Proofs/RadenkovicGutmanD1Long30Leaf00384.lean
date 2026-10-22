/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00384 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2271692609556110689435648000000000000 2096597515242765846254939815758790656 60238782464487808091291648000000000000))
theorem leaf00384_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2271692609556110689435648000000000000 2096597515242765846254939815758790656 60238782464487808091291648000000000000 raw00384=true := by decide +kernel
#print axioms leaf00384_raw
theorem leaf00384_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00384=true := by decide +kernel
#print axioms leaf00384_rectangular
def affine00384 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00384 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00384_transform : affine00384=(NestedInteger.clearedAll 3 raw00384 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00384_transform
theorem leaf00384_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00384=true := by decide +kernel
#print axioms leaf00384_sign
theorem leaf00384_log : RationalLog.accepts (3830601171/4294967296) (-122859905/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00384_log
def leaf00384 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (543824673/15625000000) (3830601171/4294967296) (-122859905/2147483648) 1 8 ![60,0,4] ![(3/320),0,(1/2)] ![(1/6400),1,(1/2)] affine00384
theorem leaf00384_checked : FastNestedCellData.accepts 1 2 4 leaf00384=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (543824673/15625000000) (3830601171/4294967296) (-122859905/2147483648) 1 8 ![60,0,4] ![(3/320),0,(1/2)] ![(1/6400),1,(1/2)] 2271692609556110689435648000000000000 2096597515242765846254939815758790656 60238782464487808091291648000000000000 raw00384 affine00384
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00384_raw leaf00384_rectangular
    leaf00384_transform leaf00384_sign leaf00384_log
#print axioms leaf00384_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
