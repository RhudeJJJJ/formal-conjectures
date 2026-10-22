/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0866 : Family 10 := level10.get ⟨603,by decide⟩
def sourceMap0866 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0866 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0866_checked : acceptsGraphIso
    (source (graph core0866) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2096.graph sourceMap0866=true := by decide +kernel
theorem fusedMap0866_checked : acceptsGraphIso
    (fused (graph core0866) (root 10) 2 2) DegreeTwoThreeSpectrum5282.graph fusedMap0866=true := by decide +kernel
theorem certified0866 : Certified (graph core0866) (root 10) 2 2 :=
  of_native_maps core0866 DegreeOneMiddleResidualSpectrum2096.graph DegreeTwoThreeSpectrum5282.graph
    sourceMap0866 fusedMap0866 sourceMap0866_checked fusedMap0866_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0866
#print axioms sourceMap0866_checked
#print axioms fusedMap0866_checked
#print axioms certified0866
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
