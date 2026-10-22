/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00348 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2920468764364456065229861683200000000000 2528464202108193419091196295494666027008 39926751318958335763349608857600000000000))
theorem leaf00348_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2920468764364456065229861683200000000000 2528464202108193419091196295494666027008 39926751318958335763349608857600000000000 raw00348=true := by decide +kernel
#print axioms leaf00348_raw
theorem leaf00348_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00348=true := by decide +kernel
#print axioms leaf00348_rectangular
def affine00348 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00348 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00348_transform : affine00348=(NestedInteger.clearedAll 3 raw00348 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00348_transform
theorem leaf00348_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00348=true := by decide +kernel
#print axioms leaf00348_sign
theorem leaf00348_log : RationalLog.accepts (3497011253/4294967296) (-55172957/536870912) 1 8=true := by decide +kernel
#print axioms leaf00348_log
def leaf00348 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3166378579/50000000000) (3497011253/4294967296) (-55172957/536870912) 1 8 ![60,0,4] ![(53/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00348
theorem leaf00348_checked : FastNestedCellData.accepts 1 2 4 leaf00348=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3166378579/50000000000) (3497011253/4294967296) (-55172957/536870912) 1 8 ![60,0,4] ![(53/6400),0,(1/4)] ![(1/6400),1,(1/4)] 2920468764364456065229861683200000000000 2528464202108193419091196295494666027008 39926751318958335763349608857600000000000 raw00348 affine00348
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00348_raw leaf00348_rectangular
    leaf00348_transform leaf00348_sign leaf00348_log
#print axioms leaf00348_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
