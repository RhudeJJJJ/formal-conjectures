/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00238 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 343407485830303375335828226048000000000000 194151290272184855098182167008348630679552 651823873788762913431275700224000000000000))
theorem leaf00238_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 343407485830303375335828226048000000000000 194151290272184855098182167008348630679552 651823873788762913431275700224000000000000 raw00238=true := by decide +kernel
#print axioms leaf00238_raw
theorem leaf00238_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00238=true := by decide +kernel
#print axioms leaf00238_rectangular
def affine00238 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00238 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00238_transform : affine00238=(NestedInteger.clearedAll 3 raw00238 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00238_transform
theorem leaf00238_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00238=true := by decide +kernel
#print axioms leaf00238_sign
theorem leaf00238_log : RationalLog.accepts (1870953673/4294967296) (-1784549651/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00238_log
def leaf00238 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (74464628437/250000000000) (1870953673/4294967296) (-1784549651/4294967296) 2 8 ![52,0,4] ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)] affine00238
theorem leaf00238_checked : FastNestedCellData.accepts 1 0 4 leaf00238=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (74464628437/250000000000) (1870953673/4294967296) (-1784549651/4294967296) 2 8 ![52,0,4] ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)] 343407485830303375335828226048000000000000 194151290272184855098182167008348630679552 651823873788762913431275700224000000000000 raw00238 affine00238
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00238_raw leaf00238_rectangular
    leaf00238_transform leaf00238_sign leaf00238_log
#print axioms leaf00238_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
