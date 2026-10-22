/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0757 : Family 10 := level10.get ⟨398,by decide⟩
def sourceMap0757 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0757 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0757_checked : acceptsGraphIso
    (source (graph core0757) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1855.graph sourceMap0757=true := by decide +kernel
theorem fusedMap0757_checked : acceptsGraphIso
    (fused (graph core0757) (root 10) 2 2) DegreeTwoThreeSpectrum5752.graph fusedMap0757=true := by decide +kernel
theorem certified0757 : Certified (graph core0757) (root 10) 2 2 :=
  of_native_maps core0757 DegreeOneMiddleResidualSpectrum1855.graph DegreeTwoThreeSpectrum5752.graph
    sourceMap0757 fusedMap0757 sourceMap0757_checked fusedMap0757_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0757
#print axioms sourceMap0757_checked
#print axioms fusedMap0757_checked
#print axioms certified0757
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
