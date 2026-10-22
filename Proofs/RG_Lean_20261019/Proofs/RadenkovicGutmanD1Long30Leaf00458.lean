/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00458 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16393332857149970927833212518400000000000 13445486267406653667194477481902720679936 151296533952368487534791386726400000000000))
theorem leaf00458_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16393332857149970927833212518400000000000 13445486267406653667194477481902720679936 151296533952368487534791386726400000000000 raw00458=true := by decide +kernel
#print axioms leaf00458_raw
theorem leaf00458_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00458=true := by decide +kernel
#print axioms leaf00458_rectangular
def affine00458 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00458 (IntegerComputedClassCell.leftNumerator ![(3/256),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/256),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00458_transform : affine00458=(NestedInteger.clearedAll 3 raw00458 (IntegerComputedClassCell.leftNumerator ![(3/256),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/256),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00458_transform
theorem leaf00458_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00458=true := by decide +kernel
#print axioms leaf00458_sign
theorem leaf00458_log : RationalLog.accepts (3235144691/4294967296) (-304266547/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00458_log
def leaf00458 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8886843549/100000000000) (3235144691/4294967296) (-304266547/2147483648) 1 8 ![60,0,4] ![(3/256),0,(1/4)] ![(1/6400),1,(1/4)] affine00458
theorem leaf00458_checked : FastNestedCellData.accepts 1 2 4 leaf00458=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8886843549/100000000000) (3235144691/4294967296) (-304266547/2147483648) 1 8 ![60,0,4] ![(3/256),0,(1/4)] ![(1/6400),1,(1/4)] 16393332857149970927833212518400000000000 13445486267406653667194477481902720679936 151296533952368487534791386726400000000000 raw00458 affine00458
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00458_raw leaf00458_rectangular
    leaf00458_transform leaf00458_sign leaf00458_log
#print axioms leaf00458_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
