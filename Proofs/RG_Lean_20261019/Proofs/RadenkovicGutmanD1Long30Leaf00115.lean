/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00115 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4482780972697212011369463808000000000000 510462867636108494265865978351976448 2051334111101334746824704000000000000))
theorem leaf00115_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4482780972697212011369463808000000000000 510462867636108494265865978351976448 2051334111101334746824704000000000000 raw00115=true := by decide +kernel
#print axioms leaf00115_raw
theorem leaf00115_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00115=true := by decide +kernel
#print axioms leaf00115_rectangular
def affine00115 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00115 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/6400),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00115_transform : affine00115=(NestedInteger.clearedAll 3 raw00115 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/6400),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00115_transform
theorem leaf00115_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00115=true := by decide +kernel
#print axioms leaf00115_sign
theorem leaf00115_log : RationalLog.accepts (391623/4294967296) (-19977299681/4294967296) 14 8=true := by decide +kernel
#print axioms leaf00115_log
def leaf00115 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7776385391/31250000000) (391623/4294967296) (-19977299681/4294967296) 14 8 ![60,0,4] ![(17/6400),0,0] ![(3/32000),1,(1/16)] affine00115
theorem leaf00115_checked : FastNestedCellData.accepts 1 2 4 leaf00115=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7776385391/31250000000) (391623/4294967296) (-19977299681/4294967296) 14 8 ![60,0,4] ![(17/6400),0,0] ![(3/32000),1,(1/16)] 4482780972697212011369463808000000000000 510462867636108494265865978351976448 2051334111101334746824704000000000000 raw00115 affine00115
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00115_raw leaf00115_rectangular
    leaf00115_transform leaf00115_sign leaf00115_log
#print axioms leaf00115_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
