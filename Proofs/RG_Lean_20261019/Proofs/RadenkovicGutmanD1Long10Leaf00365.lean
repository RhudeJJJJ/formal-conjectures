/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00365 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 430594331152054307973849153536000000000000 360378872308091238728157274512358429949952 964918768387694531956055212032000000000000))
theorem leaf00365_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 430594331152054307973849153536000000000000 360378872308091238728157274512358429949952 964918768387694531956055212032000000000000 raw00365=true := by decide +kernel
#print axioms leaf00365_raw
theorem leaf00365_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00365=true := by decide +kernel
#print axioms leaf00365_rectangular
def affine00365 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00365 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf00365_transform : affine00365=(NestedInteger.clearedAll 3 raw00365 (IntegerComputedClassCell.leftNumerator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/80),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00365_transform
theorem leaf00365_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00365=true := by decide +kernel
#print axioms leaf00365_sign
theorem leaf00365_log : RationalLog.accepts (2617147527/4294967296) (-1063775273/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00365_log
def leaf00365 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (93370261859/250000000000) (2617147527/4294967296) (-1063775273/4294967296) 1 8 ![52,0,4] ![(19/80),0,(1/2)] ![(3/160),1,(1/2)] affine00365
theorem leaf00365_checked : FastNestedCellData.accepts 1 0 4 leaf00365=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (93370261859/250000000000) (2617147527/4294967296) (-1063775273/4294967296) 1 8 ![52,0,4] ![(19/80),0,(1/2)] ![(3/160),1,(1/2)] 430594331152054307973849153536000000000000 360378872308091238728157274512358429949952 964918768387694531956055212032000000000000 raw00365 affine00365
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00365_raw leaf00365_rectangular
    leaf00365_transform leaf00365_sign leaf00365_log
#print axioms leaf00365_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
