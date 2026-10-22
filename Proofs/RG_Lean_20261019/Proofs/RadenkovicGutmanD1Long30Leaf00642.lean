/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00642 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 23516571593653476114441437184000000000000 11943719194966242762146408660987453374464 36596987176742575654416941056000000000000))
theorem leaf00642_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 23516571593653476114441437184000000000000 11943719194966242762146408660987453374464 36596987176742575654416941056000000000000 raw00642=true := by decide +kernel
#print axioms leaf00642_raw
theorem leaf00642_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00642=true := by decide +kernel
#print axioms leaf00642_rectangular
def affine00642 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00642 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(149/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00642_transform : affine00642=(NestedInteger.clearedAll 3 raw00642 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(149/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00642_transform
theorem leaf00642_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00642=true := by decide +kernel
#print axioms leaf00642_sign
theorem leaf00642_log : RationalLog.accepts (1644616639/4294967296) (-2061448287/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00642_log
def leaf00642 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (20397374409/62500000000) (1644616639/4294967296) (-2061448287/4294967296) 2 8 ![60,0,4] ![(149/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00642
theorem leaf00642_checked : FastNestedCellData.accepts 1 2 4 leaf00642=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (20397374409/62500000000) (1644616639/4294967296) (-2061448287/4294967296) 2 8 ![60,0,4] ![(149/6400),0,(1/8)] ![(3/6400),1,(1/8)] 23516571593653476114441437184000000000000 11943719194966242762146408660987453374464 36596987176742575654416941056000000000000 raw00642 affine00642
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00642_raw leaf00642_rectangular
    leaf00642_transform leaf00642_sign leaf00642_log
#print axioms leaf00642_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
