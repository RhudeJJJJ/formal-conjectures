/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0779 : Family 10 := level10.get ⟨438,by decide⟩
def sourceMap0779 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0779 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0779_checked : acceptsGraphIso
    (source (graph core0779) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1932.graph sourceMap0779=true := by decide +kernel
theorem fusedMap0779_checked : acceptsGraphIso
    (fused (graph core0779) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1483.graph fusedMap0779=true := by decide +kernel
theorem certified0779 : Certified (graph core0779) (root 10) 2 2 :=
  of_native_maps core0779 DegreeOneMiddleResidualSpectrum1932.graph DegreeOneMiddleResidualSpectrum1483.graph
    sourceMap0779 fusedMap0779 sourceMap0779_checked fusedMap0779_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0779
#print axioms sourceMap0779_checked
#print axioms fusedMap0779_checked
#print axioms certified0779
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
