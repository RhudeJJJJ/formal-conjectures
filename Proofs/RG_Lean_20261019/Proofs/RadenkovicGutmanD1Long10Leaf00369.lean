/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00369 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8664900539060303937532283846656000000000000 7541299192590314402210064815249722582237184 16054704328328337763751243546624000000000000))
theorem leaf00369_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8664900539060303937532283846656000000000000 7541299192590314402210064815249722582237184 16054704328328337763751243546624000000000000 raw00369=true := by decide +kernel
#print axioms leaf00369_raw
theorem leaf00369_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00369=true := by decide +kernel
#print axioms leaf00369_rectangular
def affine00369 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00369 (IntegerComputedClassCell.leftNumerator ![(11/40),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/40),0,0] ![(3/80),1,(1/4)]))
theorem leaf00369_transform : affine00369=(NestedInteger.clearedAll 3 raw00369 (IntegerComputedClassCell.leftNumerator ![(11/40),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/40),0,0] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00369_transform
theorem leaf00369_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00369=true := by decide +kernel
#print axioms leaf00369_sign
theorem leaf00369_log : RationalLog.accepts (2543351059/4294967296) (-562599303/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00369_log
def leaf00369 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (469725199441/1000000000000) (2543351059/4294967296) (-562599303/2147483648) 1 8 ![52,0,4] ![(11/40),0,0] ![(3/80),1,(1/4)] affine00369
theorem leaf00369_checked : FastNestedCellData.accepts 1 0 4 leaf00369=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (469725199441/1000000000000) (2543351059/4294967296) (-562599303/2147483648) 1 8 ![52,0,4] ![(11/40),0,0] ![(3/80),1,(1/4)] 8664900539060303937532283846656000000000000 7541299192590314402210064815249722582237184 16054704328328337763751243546624000000000000 raw00369 affine00369
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00369_raw leaf00369_rectangular
    leaf00369_transform leaf00369_sign leaf00369_log
#print axioms leaf00369_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
