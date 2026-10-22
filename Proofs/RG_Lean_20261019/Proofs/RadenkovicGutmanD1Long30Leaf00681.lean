/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00681 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 137026830201252231359028946534400000000000 39026186933194871613021827486362288259072 65672000281994291858873778176000000000000))
theorem leaf00681_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 137026830201252231359028946534400000000000 39026186933194871613021827486362288259072 65672000281994291858873778176000000000000 raw00681=true := by decide +kernel
#print axioms leaf00681_raw
theorem leaf00681_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00681=true := by decide +kernel
#print axioms leaf00681_rectangular
def affine00681 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00681 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(173/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00681_transform : affine00681=(NestedInteger.clearedAll 3 raw00681 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(173/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00681_transform
theorem leaf00681_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00681=true := by decide +kernel
#print axioms leaf00681_sign
theorem leaf00681_log : RationalLog.accepts (767275715/4294967296) (-1849362517/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00681_log
def leaf00681 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (148564786993/250000000000) (767275715/4294967296) (-1849362517/2147483648) 3 8 ![60,0,4] ![(173/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00681
theorem leaf00681_checked : FastNestedCellData.accepts 1 2 4 leaf00681=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (148564786993/250000000000) (767275715/4294967296) (-1849362517/2147483648) 3 8 ![60,0,4] ![(173/6400),0,(1/16)] ![(3/6400),1,(1/16)] 137026830201252231359028946534400000000000 39026186933194871613021827486362288259072 65672000281994291858873778176000000000000 raw00681 affine00681
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00681_raw leaf00681_rectangular
    leaf00681_transform leaf00681_sign leaf00681_log
#print axioms leaf00681_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
