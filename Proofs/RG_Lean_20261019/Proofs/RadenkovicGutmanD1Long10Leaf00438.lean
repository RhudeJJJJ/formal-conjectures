/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00438 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1545542903828117462250107699200000000000 1718974642138648496792350039983683272704 205167292439360058854776976179200000000000))
theorem leaf00438_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1545542903828117462250107699200000000000 1718974642138648496792350039983683272704 205167292439360058854776976179200000000000 raw00438=true := by decide +kernel
#print axioms leaf00438_raw
theorem leaf00438_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00438=true := by decide +kernel
#print axioms leaf00438_rectangular
def affine00438 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00438 (IntegerComputedClassCell.leftNumerator ![(17/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf00438_transform : affine00438=(NestedInteger.clearedAll 3 raw00438 (IntegerComputedClassCell.leftNumerator ![(17/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00438_transform
theorem leaf00438_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00438=true := by decide +kernel
#print axioms leaf00438_sign
theorem leaf00438_log : RationalLog.accepts (4737232821/4294967296) (210473221/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00438_log
def leaf00438 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (837840487/100000000000) (4737232821/4294967296) (210473221/4294967296) 0 8 ![52,0,4] ![(17/64),0,0] ![(1/64),1,(1/2)] affine00438
theorem leaf00438_checked : FastNestedCellData.accepts 1 0 4 leaf00438=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (837840487/100000000000) (4737232821/4294967296) (210473221/4294967296) 0 8 ![52,0,4] ![(17/64),0,0] ![(1/64),1,(1/2)] 1545542903828117462250107699200000000000 1718974642138648496792350039983683272704 205167292439360058854776976179200000000000 raw00438 affine00438
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00438_raw leaf00438_rectangular
    leaf00438_transform leaf00438_sign leaf00438_log
#print axioms leaf00438_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
