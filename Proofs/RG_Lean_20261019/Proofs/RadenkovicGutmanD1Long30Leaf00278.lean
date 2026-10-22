/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00278 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3377862523420616028254633984000000000000 3030938120291775431762857852057983909888 64656896813224572879007383552000000000000))
theorem leaf00278_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3377862523420616028254633984000000000000 3030938120291775431762857852057983909888 64656896813224572879007383552000000000000 raw00278=true := by decide +kernel
#print axioms leaf00278_raw
theorem leaf00278_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00278=true := by decide +kernel
#print axioms leaf00278_rectangular
def affine00278 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00278 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00278_transform : affine00278=(NestedInteger.clearedAll 3 raw00278 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00278_transform
theorem leaf00278_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00278=true := by decide +kernel
#print axioms leaf00278_sign
theorem leaf00278_log : RationalLog.accepts (3681282913/4294967296) (-331104717/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00278_log
def leaf00278 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2929828709/62500000000) (3681282913/4294967296) (-331104717/4294967296) 1 8 ![60,0,4] ![(39/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00278
theorem leaf00278_checked : FastNestedCellData.accepts 1 2 4 leaf00278=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2929828709/62500000000) (3681282913/4294967296) (-331104717/4294967296) 1 8 ![60,0,4] ![(39/6400),0,(1/4)] ![(1/6400),1,(1/4)] 3377862523420616028254633984000000000000 3030938120291775431762857852057983909888 64656896813224572879007383552000000000000 raw00278 affine00278
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00278_raw leaf00278_rectangular
    leaf00278_transform leaf00278_sign leaf00278_log
#print axioms leaf00278_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
