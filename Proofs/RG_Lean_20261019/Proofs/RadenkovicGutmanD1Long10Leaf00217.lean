/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00217 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4848214917822697518425559793664000000000000 2876946738278308745130958822829127534379008 10946358833974082677303412785152000000000000))
theorem leaf00217_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4848214917822697518425559793664000000000000 2876946738278308745130958822829127534379008 10946358833974082677303412785152000000000000 raw00217=true := by decide +kernel
#print axioms leaf00217_raw
theorem leaf00217_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00217=true := by decide +kernel
#print axioms leaf00217_rectangular
def affine00217 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00217 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00217_transform : affine00217=(NestedInteger.clearedAll 3 raw00217 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00217_transform
theorem leaf00217_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00217=true := by decide +kernel
#print axioms leaf00217_sign
theorem leaf00217_log : RationalLog.accepts (2018215753/4294967296) (-50682637/134217728) 2 8=true := by decide +kernel
#print axioms leaf00217_log
def leaf00217 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (262822257329/1000000000000) (2018215753/4294967296) (-50682637/134217728) 2 8 ![52,0,4] ![(121/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00217
theorem leaf00217_checked : FastNestedCellData.accepts 1 0 4 leaf00217=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (262822257329/1000000000000) (2018215753/4294967296) (-50682637/134217728) 2 8 ![52,0,4] ![(121/3200),0,(1/4)] ![(3/3200),1,(1/4)] 4848214917822697518425559793664000000000000 2876946738278308745130958822829127534379008 10946358833974082677303412785152000000000000 raw00217 affine00217
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00217_raw leaf00217_rectangular
    leaf00217_transform leaf00217_sign leaf00217_log
#print axioms leaf00217_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
