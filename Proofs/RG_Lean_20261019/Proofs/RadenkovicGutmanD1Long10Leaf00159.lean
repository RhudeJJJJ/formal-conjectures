/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00159 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 497037546189020240642947678208000000000000 4372954605662778155840744352928638173184 10143445786328694821379637248000000000000))
theorem leaf00159_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 497037546189020240642947678208000000000000 4372954605662778155840744352928638173184 10143445786328694821379637248000000000000 raw00159=true := by decide +kernel
#print axioms leaf00159_raw
theorem leaf00159_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00159=true := by decide +kernel
#print axioms leaf00159_rectangular
def affine00159 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00159 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(137/6400),0,0] ![(3/6400),1,(1/4)]))
theorem leaf00159_transform : affine00159=(NestedInteger.clearedAll 3 raw00159 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(137/6400),0,0] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00159_transform
theorem leaf00159_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00159=true := by decide +kernel
#print axioms leaf00159_sign
theorem leaf00159_log : RationalLog.accepts (26404151/4294967296) (-10934295501/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00159_log
def leaf00159 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (107777837477/250000000000) (26404151/4294967296) (-10934295501/4294967296) 8 8 ![52,0,4] ![(137/6400),0,0] ![(3/6400),1,(1/4)] affine00159
theorem leaf00159_checked : FastNestedCellData.accepts 1 0 4 leaf00159=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (107777837477/250000000000) (26404151/4294967296) (-10934295501/4294967296) 8 8 ![52,0,4] ![(137/6400),0,0] ![(3/6400),1,(1/4)] 497037546189020240642947678208000000000000 4372954605662778155840744352928638173184 10143445786328694821379637248000000000000 raw00159 affine00159
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00159_raw leaf00159_rectangular
    leaf00159_transform leaf00159_sign leaf00159_log
#print axioms leaf00159_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
