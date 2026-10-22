/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0741 : Family 10 := level10.get ⟨374,by decide⟩
def sourceMap0741 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0741 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0741_checked : acceptsGraphIso
    (source (graph core0741) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1875.graph sourceMap0741=true := by decide +kernel
theorem fusedMap0741_checked : acceptsGraphIso
    (fused (graph core0741) (root 10) 2 2) DegreeTwoThreeSpectrum5686.graph fusedMap0741=true := by decide +kernel
theorem certified0741 : Certified (graph core0741) (root 10) 2 2 :=
  of_native_maps core0741 DegreeOneMiddleResidualSpectrum1875.graph DegreeTwoThreeSpectrum5686.graph
    sourceMap0741 fusedMap0741 sourceMap0741_checked fusedMap0741_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0741
#print axioms sourceMap0741_checked
#print axioms fusedMap0741_checked
#print axioms certified0741
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
