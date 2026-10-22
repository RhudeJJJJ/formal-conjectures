/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00221 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 418147425134458752060515942400000000000 301828635180672720210827581206797746176 2080514570274078225770060185600000000000))
theorem leaf00221_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 418147425134458752060515942400000000000 301828635180672720210827581206797746176 2080514570274078225770060185600000000000 raw00221=true := by decide +kernel
#print axioms leaf00221_raw
theorem leaf00221_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00221=true := by decide +kernel
#print axioms leaf00221_rectangular
def affine00221 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00221 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00221_transform : affine00221=(NestedInteger.clearedAll 3 raw00221 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00221_transform
theorem leaf00221_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00221=true := by decide +kernel
#print axioms leaf00221_sign
theorem leaf00221_log : RationalLog.accepts (2707430449/4294967296) (-990943329/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00221_log
def leaf00221 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1813425387/12500000000) (2707430449/4294967296) (-990943329/4294967296) 1 8 ![60,0,4] ![(37/8000),0,(1/16)] ![(3/32000),1,(1/16)] affine00221
theorem leaf00221_checked : FastNestedCellData.accepts 1 2 4 leaf00221=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1813425387/12500000000) (2707430449/4294967296) (-990943329/4294967296) 1 8 ![60,0,4] ![(37/8000),0,(1/16)] ![(3/32000),1,(1/16)] 418147425134458752060515942400000000000 301828635180672720210827581206797746176 2080514570274078225770060185600000000000 raw00221 affine00221
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00221_raw leaf00221_rectangular
    leaf00221_transform leaf00221_sign leaf00221_log
#print axioms leaf00221_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
