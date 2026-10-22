/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00824 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 744394005543085565466164330496000000000000 541880757548625216541197883141938456035328 3357071516741539400833797455872000000000000))
theorem leaf00824_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 744394005543085565466164330496000000000000 541880757548625216541197883141938456035328 3357071516741539400833797455872000000000000 raw00824=true := by decide +kernel
#print axioms leaf00824_raw
theorem leaf00824_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00824=true := by decide +kernel
#print axioms leaf00824_rectangular
def affine00824 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00824 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00824_transform : affine00824=(NestedInteger.clearedAll 3 raw00824 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00824_transform
theorem leaf00824_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00824=true := by decide +kernel
#print axioms leaf00824_sign
theorem leaf00824_log : RationalLog.accepts (1345994861/2147483648) (-1003225685/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00824_log
def leaf00824 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (161414719599/1000000000000) (1345994861/2147483648) (-1003225685/4294967296) 1 8 ![60,0,4] ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)] affine00824
theorem leaf00824_checked : FastNestedCellData.accepts 1 2 4 leaf00824=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (161414719599/1000000000000) (1345994861/2147483648) (-1003225685/4294967296) 1 8 ![60,0,4] ![(37/800),0,(1/2)] ![(3/3200),1,(1/2)] 744394005543085565466164330496000000000000 541880757548625216541197883141938456035328 3357071516741539400833797455872000000000000 raw00824 affine00824
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00824_raw leaf00824_rectangular
    leaf00824_transform leaf00824_sign leaf00824_log
#print axioms leaf00824_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
