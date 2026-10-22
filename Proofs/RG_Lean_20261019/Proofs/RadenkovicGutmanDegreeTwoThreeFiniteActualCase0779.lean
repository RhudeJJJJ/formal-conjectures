/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0779 : Family 10 := level10.get ⟨1162,by decide⟩
def sourceMap0779 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0779 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0779_checked : acceptsGraphIso
    (source (graph core0779) (root 10) 0 0) DegreeOneSmallSpectrum1156.graph sourceMap0779=true := by decide +kernel
theorem fusedMap0779_checked : acceptsGraphIso
    (fused (graph core0779) (root 10) 0 0) DegreeOneSmallSpectrum1155.graph fusedMap0779=true := by decide +kernel
theorem certified0779 : Certified (graph core0779) (root 10) 0 0 :=
  of_native_maps core0779 DegreeOneSmallSpectrum1156.graph DegreeOneSmallSpectrum1155.graph
    sourceMap0779 fusedMap0779 sourceMap0779_checked fusedMap0779_checked
    DegreeTwoThreeFiniteComparisons.comparison0779
#print axioms sourceMap0779_checked
#print axioms fusedMap0779_checked
#print axioms certified0779
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
