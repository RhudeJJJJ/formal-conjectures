/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0772 : Family 10 := level10.get ⟨429,by decide⟩
def sourceMap0772 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0772 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0772_checked : acceptsGraphIso
    (source (graph core0772) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1925.graph sourceMap0772=true := by decide +kernel
theorem fusedMap0772_checked : acceptsGraphIso
    (fused (graph core0772) (root 10) 2 2) DegreeTwoThreeSpectrum5825.graph fusedMap0772=true := by decide +kernel
theorem certified0772 : Certified (graph core0772) (root 10) 2 2 :=
  of_native_maps core0772 DegreeOneMiddleResidualSpectrum1925.graph DegreeTwoThreeSpectrum5825.graph
    sourceMap0772 fusedMap0772 sourceMap0772_checked fusedMap0772_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0772
#print axioms sourceMap0772_checked
#print axioms fusedMap0772_checked
#print axioms certified0772
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
