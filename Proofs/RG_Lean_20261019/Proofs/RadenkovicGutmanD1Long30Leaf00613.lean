/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00613 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 43933784126651752366886354944000000000000 31632530890226369015933413816904657666048 207527224398355963628799131648000000000000))
theorem leaf00613_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 43933784126651752366886354944000000000000 31632530890226369015933413816904657666048 207527224398355963628799131648000000000000 raw00613=true := by decide +kernel
#print axioms leaf00613_raw
theorem leaf00613_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00613=true := by decide +kernel
#print axioms leaf00613_rectangular
def affine00613 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00613 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00613_transform : affine00613=(NestedInteger.clearedAll 3 raw00613 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00613_transform
theorem leaf00613_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00613=true := by decide +kernel
#print axioms leaf00613_sign
theorem leaf00613_log : RationalLog.accepts (670844983/1073741824) (-252526247/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00613_log
def leaf00613 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (76212966713/500000000000) (670844983/1073741824) (-252526247/1073741824) 1 8 ![60,0,4] ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00613
theorem leaf00613_checked : FastNestedCellData.accepts 1 2 4 leaf00613=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (76212966713/500000000000) (670844983/1073741824) (-252526247/1073741824) 1 8 ![60,0,4] ![(131/6400),0,(1/4)] ![(3/6400),1,(1/4)] 43933784126651752366886354944000000000000 31632530890226369015933413816904657666048 207527224398355963628799131648000000000000 raw00613 affine00613
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00613_raw leaf00613_rectangular
    leaf00613_transform leaf00613_sign leaf00613_log
#print axioms leaf00613_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
