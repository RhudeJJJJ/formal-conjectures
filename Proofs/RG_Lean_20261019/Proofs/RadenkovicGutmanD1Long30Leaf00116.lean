/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00116 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1564324132363492163814502170624000000000000 1286786339351833183231294664921110479372288 15173976919799390435243397742592000000000000))
theorem leaf00116_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1564324132363492163814502170624000000000000 1286786339351833183231294664921110479372288 15173976919799390435243397742592000000000000 raw00116=true := by decide +kernel
#print axioms leaf00116_raw
theorem leaf00116_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00116=true := by decide +kernel
#print axioms leaf00116_rectangular
def affine00116 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00116 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/6400),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00116_transform : affine00116=(NestedInteger.clearedAll 3 raw00116 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/6400),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00116_transform
theorem leaf00116_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00116=true := by decide +kernel
#print axioms leaf00116_sign
theorem leaf00116_log : RationalLog.accepts (3256784393/4294967296) (-148554131/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00116_log
def leaf00116 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (84802181139/1000000000000) (3256784393/4294967296) (-148554131/1073741824) 1 8 ![60,0,4] ![(17/6400),0,(1/16)] ![(3/32000),1,(1/16)] affine00116
theorem leaf00116_checked : FastNestedCellData.accepts 1 2 4 leaf00116=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (84802181139/1000000000000) (3256784393/4294967296) (-148554131/1073741824) 1 8 ![60,0,4] ![(17/6400),0,(1/16)] ![(3/32000),1,(1/16)] 1564324132363492163814502170624000000000000 1286786339351833183231294664921110479372288 15173976919799390435243397742592000000000000 raw00116 affine00116
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00116_raw leaf00116_rectangular
    leaf00116_transform leaf00116_sign leaf00116_log
#print axioms leaf00116_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
