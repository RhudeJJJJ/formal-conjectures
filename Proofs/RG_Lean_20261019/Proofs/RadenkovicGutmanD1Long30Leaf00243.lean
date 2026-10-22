/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00243 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 445128468054653698901205319680000000000 406761547169912766314543212826695041024 10535478376138470178598944768000000000000))
theorem leaf00243_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 445128468054653698901205319680000000000 406761547169912766314543212826695041024 10535478376138470178598944768000000000000 raw00243=true := by decide +kernel
#print axioms leaf00243_raw
theorem leaf00243_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00243=true := by decide +kernel
#print axioms leaf00243_rectangular
def affine00243 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00243 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00243_transform : affine00243=(NestedInteger.clearedAll 3 raw00243 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00243_transform
theorem leaf00243_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00243=true := by decide +kernel
#print axioms leaf00243_sign
theorem leaf00243_log : RationalLog.accepts (3778873975/4294967296) (-137458155/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00243_log
def leaf00243 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4826092521/125000000000) (3778873975/4294967296) (-137458155/2147483648) 1 8 ![60,0,4] ![(1/200),0,(1/4)] ![(1/6400),1,(1/4)] affine00243
theorem leaf00243_checked : FastNestedCellData.accepts 1 2 4 leaf00243=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4826092521/125000000000) (3778873975/4294967296) (-137458155/2147483648) 1 8 ![60,0,4] ![(1/200),0,(1/4)] ![(1/6400),1,(1/4)] 445128468054653698901205319680000000000 406761547169912766314543212826695041024 10535478376138470178598944768000000000000 raw00243 affine00243
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00243_raw leaf00243_rectangular
    leaf00243_transform leaf00243_sign leaf00243_log
#print axioms leaf00243_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
