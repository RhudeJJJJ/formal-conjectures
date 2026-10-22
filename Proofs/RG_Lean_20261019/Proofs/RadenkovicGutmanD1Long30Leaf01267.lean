/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01267 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 2823442250611176849924528537600000000000 2991965397332537468780490292365971423232 977388858405743566604474515456000000000000))
theorem leaf01267_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 2823442250611176849924528537600000000000 2991965397332537468780490292365971423232 977388858405743566604474515456000000000000 raw01267=true := by decide +kernel
#print axioms leaf01267_raw
theorem leaf01267_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01267=true := by decide +kernel
#print axioms leaf01267_rectangular
def affine01267 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01267 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/16),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01267_transform : affine01267=(NestedInteger.clearedAll 3 raw01267 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/16),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01267_transform
theorem leaf01267_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01267=true := by decide +kernel
#print axioms leaf01267_sign
theorem leaf01267_log : RationalLog.accepts (4537431635/4294967296) (117933771/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01267_log
def leaf01267 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1530591111/500000000000) (4537431635/4294967296) (117933771/4294967296) 0 8 ![60,0,4] ![(3/16),0,(3/4)] ![(1/128),1,(1/8)] affine01267
theorem leaf01267_checked : FastNestedCellData.accepts 1 2 4 leaf01267=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1530591111/500000000000) (4537431635/4294967296) (117933771/4294967296) 0 8 ![60,0,4] ![(3/16),0,(3/4)] ![(1/128),1,(1/8)] 2823442250611176849924528537600000000000 2991965397332537468780490292365971423232 977388858405743566604474515456000000000000 raw01267 affine01267
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01267_raw leaf01267_rectangular
    leaf01267_transform leaf01267_sign leaf01267_log
#print axioms leaf01267_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
