/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00795 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16246363292963702515779686629376000000000000 1028446410372526875423440470526841933791232 1167737504299428053380509990912000000000000))
theorem leaf00795_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16246363292963702515779686629376000000000000 1028446410372526875423440470526841933791232 1167737504299428053380509990912000000000000 raw00795=true := by decide +kernel
#print axioms leaf00795_raw
theorem leaf00795_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00795=true := by decide +kernel
#print axioms leaf00795_rectangular
def affine00795 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00795 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(133/3200),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00795_transform : affine00795=(NestedInteger.clearedAll 3 raw00795 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(133/3200),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00795_transform
theorem leaf00795_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00795=true := by decide +kernel
#print axioms leaf00795_sign
theorem leaf00795_log : RationalLog.accepts (144564577/4294967296) (-7283132799/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00795_log
def leaf00795 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (880717118861/1000000000000) (144564577/4294967296) (-7283132799/4294967296) 5 8 ![60,0,4] ![(133/3200),0,0] ![(3/3200),1,(1/16)] affine00795
theorem leaf00795_checked : FastNestedCellData.accepts 1 2 4 leaf00795=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (880717118861/1000000000000) (144564577/4294967296) (-7283132799/4294967296) 5 8 ![60,0,4] ![(133/3200),0,0] ![(3/3200),1,(1/16)] 16246363292963702515779686629376000000000000 1028446410372526875423440470526841933791232 1167737504299428053380509990912000000000000 raw00795 affine00795
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00795_raw leaf00795_rectangular
    leaf00795_transform leaf00795_sign leaf00795_log
#print axioms leaf00795_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
