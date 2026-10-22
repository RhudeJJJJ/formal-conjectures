/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00500 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 90561984186867829964800000000000 90562156893732861280543209160704 57646185164693100751459713024000000000000))
theorem leaf00500_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 90561984186867829964800000000000 90562156893732861280543209160704 57646185164693100751459713024000000000000 raw00500=true := by decide +kernel
#print axioms leaf00500_raw
theorem leaf00500_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00500=true := by decide +kernel
#print axioms leaf00500_rectangular
def affine00500 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00500 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1]))
theorem leaf00500_transform : affine00500=(NestedInteger.clearedAll 3 raw00500 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1])) := by decide +kernel
#print axioms leaf00500_transform
theorem leaf00500_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00500=true := by decide +kernel
#print axioms leaf00500_sign
theorem leaf00500_log : RationalLog.accepts (536871935/536870912) (4091/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00500_log
def leaf00500 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![52,0,4] ![(1/1024),0,0] ![(1/1024),1,1] affine00500
theorem leaf00500_checked : FastNestedCellData.accepts 1 0 4 leaf00500=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![52,0,4] ![(1/1024),0,0] ![(1/1024),1,1] 90561984186867829964800000000000 90562156893732861280543209160704 57646185164693100751459713024000000000000 raw00500 affine00500
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00500_raw leaf00500_rectangular
    leaf00500_transform leaf00500_sign leaf00500_log
#print axioms leaf00500_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
