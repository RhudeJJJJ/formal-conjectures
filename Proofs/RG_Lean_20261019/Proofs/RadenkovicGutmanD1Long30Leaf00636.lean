/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00636 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2514968464381541249258673405952000000000000 784666232041400820390344035263047129890816 1438838833443301677434385989632000000000000))
theorem leaf00636_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2514968464381541249258673405952000000000000 784666232041400820390344035263047129890816 1438838833443301677434385989632000000000000 raw00636=true := by decide +kernel
#print axioms leaf00636_raw
theorem leaf00636_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00636=true := by decide +kernel
#print axioms leaf00636_rectangular
def affine00636 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00636 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00636_transform : affine00636=(NestedInteger.clearedAll 3 raw00636 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00636_transform
theorem leaf00636_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00636=true := by decide +kernel
#print axioms leaf00636_sign
theorem leaf00636_log : RationalLog.accepts (433567093/2147483648) (-3435985721/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00636_log
def leaf00636 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (545346854563/1000000000000) (433567093/2147483648) (-3435985721/4294967296) 3 8 ![60,0,4] ![(73/3200),0,(1/16)] ![(3/6400),1,(1/16)] affine00636
theorem leaf00636_checked : FastNestedCellData.accepts 1 2 4 leaf00636=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (545346854563/1000000000000) (433567093/2147483648) (-3435985721/4294967296) 3 8 ![60,0,4] ![(73/3200),0,(1/16)] ![(3/6400),1,(1/16)] 2514968464381541249258673405952000000000000 784666232041400820390344035263047129890816 1438838833443301677434385989632000000000000 raw00636 affine00636
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00636_raw leaf00636_rectangular
    leaf00636_transform leaf00636_sign leaf00636_log
#print axioms leaf00636_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
