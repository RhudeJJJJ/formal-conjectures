/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00394 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 42178604622387807239684698931200000000000 54876911526094870931744279987483767209984 252635030819732421776555114496000000000000))
theorem leaf00394_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 42178604622387807239684698931200000000000 54876911526094870931744279987483767209984 252635030819732421776555114496000000000000 raw00394=true := by decide +kernel
#print axioms leaf00394_raw
theorem leaf00394_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00394=true := by decide +kernel
#print axioms leaf00394_rectangular
def affine00394 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00394 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf00394_transform : affine00394=(NestedInteger.clearedAll 3 raw00394 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00394_transform
theorem leaf00394_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00394=true := by decide +kernel
#print axioms leaf00394_sign
theorem leaf00394_log : RationalLog.accepts (4590805555/4294967296) (143047257/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00394_log
def leaf00394 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (217218140129/1000000000000) (4590805555/4294967296) (143047257/4294967296) 0 8 ![52,0,4] ![(5/8),0,(1/2)] ![(1/16),1,(1/4)] affine00394
theorem leaf00394_checked : FastNestedCellData.accepts 1 0 4 leaf00394=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (217218140129/1000000000000) (4590805555/4294967296) (143047257/4294967296) 0 8 ![52,0,4] ![(5/8),0,(1/2)] ![(1/16),1,(1/4)] 42178604622387807239684698931200000000000 54876911526094870931744279987483767209984 252635030819732421776555114496000000000000 raw00394 affine00394
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00394_raw leaf00394_rectangular
    leaf00394_transform leaf00394_sign leaf00394_log
#print axioms leaf00394_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
