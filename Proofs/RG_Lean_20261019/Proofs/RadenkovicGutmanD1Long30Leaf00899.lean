/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00899 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 64772777127910540195286482944000000000 43996169659702602070389502882130952192 200475846285448738517924446208000000000))
theorem leaf00899_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 64772777127910540195286482944000000000 43996169659702602070389502882130952192 200475846285448738517924446208000000000 raw00899=true := by decide +kernel
#print axioms leaf00899_raw
theorem leaf00899_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00899=true := by decide +kernel
#print axioms leaf00899_rectangular
def affine00899 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00899 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00899_transform : affine00899=(NestedInteger.clearedAll 3 raw00899 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00899_transform
theorem leaf00899_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00899=true := by decide +kernel
#print axioms leaf00899_sign
theorem leaf00899_log : RationalLog.accepts (2392297097/4294967296) (-1256685795/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00899_log
def leaf00899 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (877834821/4000000000) (2392297097/4294967296) (-1256685795/4294967296) 1 8 ![60,0,4] ![(43/640),0,(1/2)] ![(1/640),1,(1/2)] affine00899
theorem leaf00899_checked : FastNestedCellData.accepts 1 2 4 leaf00899=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (877834821/4000000000) (2392297097/4294967296) (-1256685795/4294967296) 1 8 ![60,0,4] ![(43/640),0,(1/2)] ![(1/640),1,(1/2)] 64772777127910540195286482944000000000 43996169659702602070389502882130952192 200475846285448738517924446208000000000 raw00899 affine00899
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00899_raw leaf00899_rectangular
    leaf00899_transform leaf00899_sign leaf00899_log
#print axioms leaf00899_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
