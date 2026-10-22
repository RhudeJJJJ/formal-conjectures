/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0448 : Family 10 := level10.get ⟨220,by decide⟩
def sourceMap0448 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0448 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0448_checked : acceptsGraphIso
    (source (graph core0448) (root 10) 0 0) DegreeOneSmallSpectrum1060.graph sourceMap0448=true := by decide +kernel
theorem fusedMap0448_checked : acceptsGraphIso
    (fused (graph core0448) (root 10) 0 0) DegreeOneSmallSpectrum1108.graph fusedMap0448=true := by decide +kernel
theorem certified0448 : Certified (graph core0448) (root 10) 0 0 :=
  of_native_maps core0448 DegreeOneSmallSpectrum1060.graph DegreeOneSmallSpectrum1108.graph
    sourceMap0448 fusedMap0448 sourceMap0448_checked fusedMap0448_checked
    DegreeTwoThreeFiniteComparisons.comparison0448
#print axioms sourceMap0448_checked
#print axioms fusedMap0448_checked
#print axioms certified0448
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
