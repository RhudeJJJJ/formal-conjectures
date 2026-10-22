/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00330 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 42239825641801405060461101056000000000000 77099980319423772926358805738501963776 131526089366507619411296256000000000000))
theorem leaf00330_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 42239825641801405060461101056000000000000 77099980319423772926358805738501963776 131526089366507619411296256000000000000 raw00330=true := by decide +kernel
#print axioms leaf00330_raw
theorem leaf00330_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00330=true := by decide +kernel
#print axioms leaf00330_rectangular
def affine00330 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00330 (IntegerComputedClassCell.leftNumerator ![(1/128),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/128),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00330_transform : affine00330=(NestedInteger.clearedAll 3 raw00330 (IntegerComputedClassCell.leftNumerator ![(1/128),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/128),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00330_transform
theorem leaf00330_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00330=true := by decide +kernel
#print axioms leaf00330_sign
theorem leaf00330_log : RationalLog.accepts (4942371/4294967296) (-14532782503/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00330_log
def leaf00330 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (36637208581/62500000000) (4942371/4294967296) (-14532782503/4294967296) 10 8 ![60,0,4] ![(1/128),0,0] ![(1/6400),1,(1/16)] affine00330
theorem leaf00330_checked : FastNestedCellData.accepts 1 2 4 leaf00330=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (36637208581/62500000000) (4942371/4294967296) (-14532782503/4294967296) 10 8 ![60,0,4] ![(1/128),0,0] ![(1/6400),1,(1/16)] 42239825641801405060461101056000000000000 77099980319423772926358805738501963776 131526089366507619411296256000000000000 raw00330 affine00330
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00330_raw leaf00330_rectangular
    leaf00330_transform leaf00330_sign leaf00330_log
#print axioms leaf00330_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
