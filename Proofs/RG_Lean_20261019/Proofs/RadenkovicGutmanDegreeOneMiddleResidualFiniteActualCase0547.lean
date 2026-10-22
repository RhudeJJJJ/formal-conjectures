/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0547 : Family 10 := level10.get ⟨76,by decide⟩
def sourceMap0547 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0547 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0547_checked : acceptsGraphIso
    (source (graph core0547) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1696.graph sourceMap0547=true := by decide +kernel
theorem fusedMap0547_checked : acceptsGraphIso
    (fused (graph core0547) (root 10) 2 2) DegreeTwoThreeSpectrum4991.graph fusedMap0547=true := by decide +kernel
theorem certified0547 : Certified (graph core0547) (root 10) 2 2 :=
  of_native_maps core0547 DegreeOneMiddleResidualSpectrum1696.graph DegreeTwoThreeSpectrum4991.graph
    sourceMap0547 fusedMap0547 sourceMap0547_checked fusedMap0547_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0547
#print axioms sourceMap0547_checked
#print axioms fusedMap0547_checked
#print axioms certified0547
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
