/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00298 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 951670298625780515687794475008000000000000 845164394610795856172235973357200304242688 16382282088775777291289258622976000000000000))
theorem leaf00298_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 951670298625780515687794475008000000000000 845164394610795856172235973357200304242688 16382282088775777291289258622976000000000000 raw00298=true := by decide +kernel
#print axioms leaf00298_raw
theorem leaf00298_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00298=true := by decide +kernel
#print axioms leaf00298_rectangular
def affine00298 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00298 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00298_transform : affine00298=(NestedInteger.clearedAll 3 raw00298 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00298_transform
theorem leaf00298_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00298=true := by decide +kernel
#print axioms leaf00298_sign
theorem leaf00298_log : RationalLog.accepts (3627170987/4294967296) (-181452657/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00298_log
def leaf00298 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (51590150263/1000000000000) (3627170987/4294967296) (-181452657/2147483648) 1 8 ![60,0,4] ![(43/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00298
theorem leaf00298_checked : FastNestedCellData.accepts 1 2 4 leaf00298=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (51590150263/1000000000000) (3627170987/4294967296) (-181452657/2147483648) 1 8 ![60,0,4] ![(43/6400),0,(1/4)] ![(1/6400),1,(1/4)] 951670298625780515687794475008000000000000 845164394610795856172235973357200304242688 16382282088775777291289258622976000000000000 raw00298 affine00298
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00298_raw leaf00298_rectangular
    leaf00298_transform leaf00298_sign leaf00298_log
#print axioms leaf00298_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
