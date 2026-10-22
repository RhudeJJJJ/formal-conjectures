/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0891 : Family 10 := level10.get ⟨654,by decide⟩
def sourceMap0891 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0891 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0891_checked : acceptsGraphIso
    (source (graph core0891) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2134.graph sourceMap0891=true := by decide +kernel
theorem fusedMap0891_checked : acceptsGraphIso
    (fused (graph core0891) (root 10) 2 2) DegreeTwoThreeSpectrum5363.graph fusedMap0891=true := by decide +kernel
theorem certified0891 : Certified (graph core0891) (root 10) 2 2 :=
  of_native_maps core0891 DegreeOneMiddleResidualSpectrum2134.graph DegreeTwoThreeSpectrum5363.graph
    sourceMap0891 fusedMap0891 sourceMap0891_checked fusedMap0891_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0891
#print axioms sourceMap0891_checked
#print axioms fusedMap0891_checked
#print axioms certified0891
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
