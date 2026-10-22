/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01056 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 459622001323892828716700532736000000000000 429732003427831513371258549123043643359232 1077945064732859805829129306112000000000000))
theorem leaf01056_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 459622001323892828716700532736000000000000 429732003427831513371258549123043643359232 1077945064732859805829129306112000000000000 raw01056=true := by decide +kernel
#print axioms leaf01056_raw
theorem leaf01056_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01056=true := by decide +kernel
#print axioms leaf01056_rectangular
def affine01056 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01056 (IntegerComputedClassCell.leftNumerator ![(47/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/160),0,(1/16)] ![(3/160),1,(1/16)]))
theorem leaf01056_transform : affine01056=(NestedInteger.clearedAll 3 raw01056 (IntegerComputedClassCell.leftNumerator ![(47/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/160),0,(1/16)] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01056_transform
theorem leaf01056_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01056=true := by decide +kernel
#print axioms leaf01056_sign
theorem leaf01056_log : RationalLog.accepts (1435539191/2147483648) (-864912473/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01056_log
def leaf01056 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (199329268943/500000000000) (1435539191/2147483648) (-864912473/4294967296) 1 8 ![60,0,4] ![(47/160),0,(1/16)] ![(3/160),1,(1/16)] affine01056
theorem leaf01056_checked : FastNestedCellData.accepts 1 2 4 leaf01056=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (199329268943/500000000000) (1435539191/2147483648) (-864912473/4294967296) 1 8 ![60,0,4] ![(47/160),0,(1/16)] ![(3/160),1,(1/16)] 459622001323892828716700532736000000000000 429732003427831513371258549123043643359232 1077945064732859805829129306112000000000000 raw01056 affine01056
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01056_raw leaf01056_rectangular
    leaf01056_transform leaf01056_sign leaf01056_log
#print axioms leaf01056_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
