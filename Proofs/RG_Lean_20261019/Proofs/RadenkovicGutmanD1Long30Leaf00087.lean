/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00087 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12793275834065390395732262912000000000000 11826439635395952130725617100063378505728 355263623261530609078132277248000000000000))
theorem leaf00087_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12793275834065390395732262912000000000000 11826439635395952130725617100063378505728 355263623261530609078132277248000000000000 raw00087=true := by decide +kernel
#print axioms leaf00087_raw
theorem leaf00087_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00087=true := by decide +kernel
#print axioms leaf00087_rectangular
def affine00087 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00087 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(67/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00087_transform : affine00087=(NestedInteger.clearedAll 3 raw00087 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(67/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00087_transform
theorem leaf00087_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00087=true := by decide +kernel
#print axioms leaf00087_sign
theorem leaf00087_log : RationalLog.accepts (1921233867/2147483648) (-239077547/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00087_log
def leaf00087 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16644596943/500000000000) (1921233867/2147483648) (-239077547/4294967296) 1 8 ![60,0,4] ![(67/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00087
theorem leaf00087_checked : FastNestedCellData.accepts 1 2 4 leaf00087=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16644596943/500000000000) (1921233867/2147483648) (-239077547/4294967296) 1 8 ![60,0,4] ![(67/32000),0,(1/8)] ![(3/32000),1,(1/8)] 12793275834065390395732262912000000000000 11826439635395952130725617100063378505728 355263623261530609078132277248000000000000 raw00087 affine00087
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00087_raw leaf00087_rectangular
    leaf00087_transform leaf00087_sign leaf00087_log
#print axioms leaf00087_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
