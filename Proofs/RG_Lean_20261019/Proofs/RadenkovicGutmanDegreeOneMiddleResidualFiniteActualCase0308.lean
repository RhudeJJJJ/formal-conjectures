/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0308 : Family 9 := level9.get ⟨158,by decide⟩
def sourceMap0308 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0308 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0308_checked : acceptsGraphIso
    (source (graph core0308) (root 9) 2 2) DegreeOneMiddleResidualSpectrum778.graph sourceMap0308=true := by decide +kernel
theorem fusedMap0308_checked : acceptsGraphIso
    (fused (graph core0308) (root 9) 2 2) DegreeTwoThreeSpectrum3919.graph fusedMap0308=true := by decide +kernel
theorem certified0308 : Certified (graph core0308) (root 9) 2 2 :=
  of_native_maps core0308 DegreeOneMiddleResidualSpectrum778.graph DegreeTwoThreeSpectrum3919.graph
    sourceMap0308 fusedMap0308 sourceMap0308_checked fusedMap0308_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0308
#print axioms sourceMap0308_checked
#print axioms fusedMap0308_checked
#print axioms certified0308
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
