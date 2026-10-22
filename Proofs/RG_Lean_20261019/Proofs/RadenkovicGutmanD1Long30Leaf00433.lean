/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00433 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 127747768755602430055449362432000000000000 106047129199534321182499859584499872432128 1276098121028584749042575081472000000000000))
theorem leaf00433_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 127747768755602430055449362432000000000000 106047129199534321182499859584499872432128 1276098121028584749042575081472000000000000 raw00433=true := by decide +kernel
#print axioms leaf00433_raw
theorem leaf00433_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00433=true := by decide +kernel
#print axioms leaf00433_rectangular
def affine00433 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00433 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00433_transform : affine00433=(NestedInteger.clearedAll 3 raw00433 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00433_transform
theorem leaf00433_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00433=true := by decide +kernel
#print axioms leaf00433_sign
theorem leaf00433_log : RationalLog.accepts (1645909083/2147483648) (-285619525/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00433_log
def leaf00433 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (83102645049/1000000000000) (1645909083/2147483648) (-285619525/2147483648) 1 8 ![60,0,4] ![(7/640),0,(1/4)] ![(1/6400),1,(1/4)] affine00433
theorem leaf00433_checked : FastNestedCellData.accepts 1 2 4 leaf00433=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (83102645049/1000000000000) (1645909083/2147483648) (-285619525/2147483648) 1 8 ![60,0,4] ![(7/640),0,(1/4)] ![(1/6400),1,(1/4)] 127747768755602430055449362432000000000000 106047129199534321182499859584499872432128 1276098121028584749042575081472000000000000 raw00433 affine00433
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00433_raw leaf00433_rectangular
    leaf00433_transform leaf00433_sign leaf00433_log
#print axioms leaf00433_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
