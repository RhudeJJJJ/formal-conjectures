/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0321 : Family 9 := level9.get ⟨177,by decide⟩
def sourceMap0321 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0321 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0321_checked : acceptsGraphIso
    (source (graph core0321) (root 9) 2 2) DegreeOneMiddleResidualSpectrum806.graph sourceMap0321=true := by decide +kernel
theorem fusedMap0321_checked : acceptsGraphIso
    (fused (graph core0321) (root 9) 2 2) DegreeTwoThreeSpectrum3944.graph fusedMap0321=true := by decide +kernel
theorem certified0321 : Certified (graph core0321) (root 9) 2 2 :=
  of_native_maps core0321 DegreeOneMiddleResidualSpectrum806.graph DegreeTwoThreeSpectrum3944.graph
    sourceMap0321 fusedMap0321 sourceMap0321_checked fusedMap0321_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0321
#print axioms sourceMap0321_checked
#print axioms fusedMap0321_checked
#print axioms certified0321
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
