/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00411 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 105796944248798382284341248000000000000 141458233821102036079567469939081084928 2049920443270235277982957568000000000000))
theorem leaf00411_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 105796944248798382284341248000000000000 141458233821102036079567469939081084928 2049920443270235277982957568000000000000 raw00411=true := by decide +kernel
#print axioms leaf00411_raw
theorem leaf00411_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00411=true := by decide +kernel
#print axioms leaf00411_rectangular
def affine00411 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00411 (IntegerComputedClassCell.leftNumerator ![(5/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/8),0,0] ![(1/8),1,(1/2)]))
theorem leaf00411_transform : affine00411=(NestedInteger.clearedAll 3 raw00411 (IntegerComputedClassCell.leftNumerator ![(5/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/8),0,0] ![(1/8),1,(1/2)])) := by decide +kernel
#print axioms leaf00411_transform
theorem leaf00411_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00411=true := by decide +kernel
#print axioms leaf00411_sign
theorem leaf00411_log : RationalLog.accepts (335748871/268435456) (480505855/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00411_log
def leaf00411 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (69006694521/1000000000000) (335748871/268435456) (480505855/4294967296) 0 8 ![52,0,4] ![(5/8),0,0] ![(1/8),1,(1/2)] affine00411
theorem leaf00411_checked : FastNestedCellData.accepts 1 0 4 leaf00411=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (69006694521/1000000000000) (335748871/268435456) (480505855/4294967296) 0 8 ![52,0,4] ![(5/8),0,0] ![(1/8),1,(1/2)] 105796944248798382284341248000000000000 141458233821102036079567469939081084928 2049920443270235277982957568000000000000 raw00411 affine00411
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00411_raw leaf00411_rectangular
    leaf00411_transform leaf00411_sign leaf00411_log
#print axioms leaf00411_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
