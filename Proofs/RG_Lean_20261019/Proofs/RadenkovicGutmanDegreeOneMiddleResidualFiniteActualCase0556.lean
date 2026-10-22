/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0556 : Family 10 := level10.get ⟨90,by decide⟩
def sourceMap0556 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0556 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0556_checked : acceptsGraphIso
    (source (graph core0556) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1748.graph sourceMap0556=true := by decide +kernel
theorem fusedMap0556_checked : acceptsGraphIso
    (fused (graph core0556) (root 10) 2 2) DegreeTwoThreeSpectrum5011.graph fusedMap0556=true := by decide +kernel
theorem certified0556 : Certified (graph core0556) (root 10) 2 2 :=
  of_native_maps core0556 DegreeOneMiddleResidualSpectrum1748.graph DegreeTwoThreeSpectrum5011.graph
    sourceMap0556 fusedMap0556 sourceMap0556_checked fusedMap0556_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0556
#print axioms sourceMap0556_checked
#print axioms fusedMap0556_checked
#print axioms certified0556
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
