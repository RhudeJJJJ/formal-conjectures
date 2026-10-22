/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0894 : Family 10 := level10.get ⟨658,by decide⟩
def sourceMap0894 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0894 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0894_checked : acceptsGraphIso
    (source (graph core0894) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2137.graph sourceMap0894=true := by decide +kernel
theorem fusedMap0894_checked : acceptsGraphIso
    (fused (graph core0894) (root 10) 2 2) DegreeTwoThreeSpectrum5368.graph fusedMap0894=true := by decide +kernel
theorem certified0894 : Certified (graph core0894) (root 10) 2 2 :=
  of_native_maps core0894 DegreeOneMiddleResidualSpectrum2137.graph DegreeTwoThreeSpectrum5368.graph
    sourceMap0894 fusedMap0894 sourceMap0894_checked fusedMap0894_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0894
#print axioms sourceMap0894_checked
#print axioms fusedMap0894_checked
#print axioms certified0894
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
