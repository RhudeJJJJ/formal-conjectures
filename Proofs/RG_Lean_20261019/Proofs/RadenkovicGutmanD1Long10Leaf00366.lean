/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00366 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2317474922384545499214537293824000000000000 1912316065731097374139322911666425764511744 3805435466836438276638165172224000000000000))
theorem leaf00366_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2317474922384545499214537293824000000000000 1912316065731097374139322911666425764511744 3805435466836438276638165172224000000000000 raw00366=true := by decide +kernel
#print axioms leaf00366_raw
theorem leaf00366_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00366=true := by decide +kernel
#print axioms leaf00366_rectangular
def affine00366 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00366 (IntegerComputedClassCell.leftNumerator ![(41/160),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/160),0,0] ![(3/160),1,(1/4)]))
theorem leaf00366_transform : affine00366=(NestedInteger.clearedAll 3 raw00366 (IntegerComputedClassCell.leftNumerator ![(41/160),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/160),0,0] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00366_transform
theorem leaf00366_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00366=true := by decide +kernel
#print axioms leaf00366_sign
theorem leaf00366_log : RationalLog.accepts (2358759021/4294967296) (-160875601/536870912) 1 8=true := by decide +kernel
#print axioms leaf00366_log
def leaf00366 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (251261134553/500000000000) (2358759021/4294967296) (-160875601/536870912) 1 8 ![52,0,4] ![(41/160),0,0] ![(3/160),1,(1/4)] affine00366
theorem leaf00366_checked : FastNestedCellData.accepts 1 0 4 leaf00366=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (251261134553/500000000000) (2358759021/4294967296) (-160875601/536870912) 1 8 ![52,0,4] ![(41/160),0,0] ![(3/160),1,(1/4)] 2317474922384545499214537293824000000000000 1912316065731097374139322911666425764511744 3805435466836438276638165172224000000000000 raw00366 affine00366
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00366_raw leaf00366_rectangular
    leaf00366_transform leaf00366_sign leaf00366_log
#print axioms leaf00366_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
