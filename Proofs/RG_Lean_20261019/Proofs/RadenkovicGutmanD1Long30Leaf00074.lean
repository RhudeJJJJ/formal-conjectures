/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00074 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4056927016011681578960814080000000000 3988930147231860148239078049561182208 566798876214356529663233228800000000000))
theorem leaf00074_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4056927016011681578960814080000000000 3988930147231860148239078049561182208 566798876214356529663233228800000000000 raw00074=true := by decide +kernel
#print axioms leaf00074_raw
theorem leaf00074_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00074=true := by decide +kernel
#print axioms leaf00074_rectangular
def affine00074 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00074 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/1600),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00074_transform : affine00074=(NestedInteger.clearedAll 3 raw00074 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/1600),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00074_transform
theorem leaf00074_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00074=true := by decide +kernel
#print axioms leaf00074_sign
theorem leaf00074_log : RationalLog.accepts (262091785/268435456) (-25679339/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00074_log
def leaf00074 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1407529307/200000000000) (262091785/268435456) (-25679339/2147483648) 1 8 ![60,0,4] ![(3/1600),0,(1/2)] ![(1/16000),1,(1/2)] affine00074
theorem leaf00074_checked : FastNestedCellData.accepts 1 2 4 leaf00074=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1407529307/200000000000) (262091785/268435456) (-25679339/2147483648) 1 8 ![60,0,4] ![(3/1600),0,(1/2)] ![(1/16000),1,(1/2)] 4056927016011681578960814080000000000 3988930147231860148239078049561182208 566798876214356529663233228800000000000 raw00074 affine00074
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00074_raw leaf00074_rectangular
    leaf00074_transform leaf00074_sign leaf00074_log
#print axioms leaf00074_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
