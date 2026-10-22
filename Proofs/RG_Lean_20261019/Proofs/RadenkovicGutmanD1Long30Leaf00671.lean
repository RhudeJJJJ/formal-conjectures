/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00671 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 526436694131191660050540134400000000000 152604114694031022005281159070764498944 261101796942737678157217792000000000000))
theorem leaf00671_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 526436694131191660050540134400000000000 152604114694031022005281159070764498944 261101796942737678157217792000000000000 raw00671=true := by decide +kernel
#print axioms leaf00671_raw
theorem leaf00671_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00671=true := by decide +kernel
#print axioms leaf00671_rectangular
def affine00671 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00671 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(167/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00671_transform : affine00671=(NestedInteger.clearedAll 3 raw00671 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(167/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00671_transform
theorem leaf00671_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00671=true := by decide +kernel
#print axioms leaf00671_sign
theorem leaf00671_log : RationalLog.accepts (196443695/1073741824) (-3647563377/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00671_log
def leaf00671 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (36528883677/62500000000) (196443695/1073741824) (-3647563377/4294967296) 3 8 ![60,0,4] ![(167/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00671
theorem leaf00671_checked : FastNestedCellData.accepts 1 2 4 leaf00671=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (36528883677/62500000000) (196443695/1073741824) (-3647563377/4294967296) 3 8 ![60,0,4] ![(167/6400),0,(1/16)] ![(3/6400),1,(1/16)] 526436694131191660050540134400000000000 152604114694031022005281159070764498944 261101796942737678157217792000000000000 raw00671 affine00671
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00671_raw leaf00671_rectangular
    leaf00671_transform leaf00671_sign leaf00671_log
#print axioms leaf00671_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
