/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00303 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 973377031112810882132894285824000000000000 862225639350861520676398084199844876910592 16340282536472316072659599228928000000000000))
theorem leaf00303_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 973377031112810882132894285824000000000000 862225639350861520676398084199844876910592 16340282536472316072659599228928000000000000 raw00303=true := by decide +kernel
#print axioms leaf00303_raw
theorem leaf00303_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00303=true := by decide +kernel
#print axioms leaf00303_rectangular
def affine00303 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00303 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00303_transform : affine00303=(NestedInteger.clearedAll 3 raw00303 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00303_transform
theorem leaf00303_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00303=true := by decide +kernel
#print axioms leaf00303_sign
theorem leaf00303_log : RationalLog.accepts (3613828087/4294967296) (-185409803/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00303_log
def leaf00303 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (52766874589/1000000000000) (3613828087/4294967296) (-185409803/2147483648) 1 8 ![60,0,4] ![(11/1600),0,(1/4)] ![(1/6400),1,(1/4)] affine00303
theorem leaf00303_checked : FastNestedCellData.accepts 1 2 4 leaf00303=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (52766874589/1000000000000) (3613828087/4294967296) (-185409803/2147483648) 1 8 ![60,0,4] ![(11/1600),0,(1/4)] ![(1/6400),1,(1/4)] 973377031112810882132894285824000000000000 862225639350861520676398084199844876910592 16340282536472316072659599228928000000000000 raw00303 affine00303
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00303_raw leaf00303_rectangular
    leaf00303_transform leaf00303_sign leaf00303_log
#print axioms leaf00303_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
