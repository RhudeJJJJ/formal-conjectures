/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00935 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 37321063868225176374302023352320000000000 9002866050921467008298821409640642772992 11124653798563741561597722624000000000000))
theorem leaf00935_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 37321063868225176374302023352320000000000 9002866050921467008298821409640642772992 11124653798563741561597722624000000000000 raw00935=true := by decide +kernel
#print axioms leaf00935_raw
theorem leaf00935_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00935=true := by decide +kernel
#print axioms leaf00935_rectangular
def affine00935 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00935 (IntegerComputedClassCell.leftNumerator ![(7/80),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/80),0,0] ![(1/320),1,(1/16)]))
theorem leaf00935_transform : affine00935=(NestedInteger.clearedAll 3 raw00935 (IntegerComputedClassCell.leftNumerator ![(7/80),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/80),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00935_transform
theorem leaf00935_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00935=true := by decide +kernel
#print axioms leaf00935_sign
theorem leaf00935_log : RationalLog.accepts (572641575/4294967296) (-2163524569/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00935_log
def leaf00935 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (202317892627/250000000000) (572641575/4294967296) (-2163524569/2147483648) 3 8 ![60,0,4] ![(7/80),0,0] ![(1/320),1,(1/16)] affine00935
theorem leaf00935_checked : FastNestedCellData.accepts 1 2 4 leaf00935=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (202317892627/250000000000) (572641575/4294967296) (-2163524569/2147483648) 3 8 ![60,0,4] ![(7/80),0,0] ![(1/320),1,(1/16)] 37321063868225176374302023352320000000000 9002866050921467008298821409640642772992 11124653798563741561597722624000000000000 raw00935 affine00935
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00935_raw leaf00935_rectangular
    leaf00935_transform leaf00935_sign leaf00935_log
#print axioms leaf00935_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
