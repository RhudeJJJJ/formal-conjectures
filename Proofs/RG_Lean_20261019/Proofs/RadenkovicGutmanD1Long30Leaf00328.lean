/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00328 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4225516792091307359479005184000000000000 3695539410906391802744258071406466564096 63019907794630284222538973184000000000000))
theorem leaf00328_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4225516792091307359479005184000000000000 3695539410906391802744258071406466564096 63019907794630284222538973184000000000000 raw00328=true := by decide +kernel
#print axioms leaf00328_raw
theorem leaf00328_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00328=true := by decide +kernel
#print axioms leaf00328_rectangular
def affine00328 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00328 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(49/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00328_transform : affine00328=(NestedInteger.clearedAll 3 raw00328 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(49/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00328_transform
theorem leaf00328_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00328=true := by decide +kernel
#print axioms leaf00328_sign
theorem leaf00328_log : RationalLog.accepts (221763081/268435456) (-51271415/536870912) 1 8=true := by decide +kernel
#print axioms leaf00328_log
def leaf00328 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (58640825419/1000000000000) (221763081/268435456) (-51271415/536870912) 1 8 ![60,0,4] ![(49/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00328
theorem leaf00328_checked : FastNestedCellData.accepts 1 2 4 leaf00328=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (58640825419/1000000000000) (221763081/268435456) (-51271415/536870912) 1 8 ![60,0,4] ![(49/6400),0,(1/4)] ![(1/6400),1,(1/4)] 4225516792091307359479005184000000000000 3695539410906391802744258071406466564096 63019907794630284222538973184000000000000 raw00328 affine00328
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00328_raw leaf00328_rectangular
    leaf00328_transform leaf00328_sign leaf00328_log
#print axioms leaf00328_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
