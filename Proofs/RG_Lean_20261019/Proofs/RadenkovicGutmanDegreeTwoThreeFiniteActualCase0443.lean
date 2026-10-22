/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0443 : Family 10 := level10.get ⟨200,by decide⟩
def sourceMap0443 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0443 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0443_checked : acceptsGraphIso
    (source (graph core0443) (root 10) 0 0) DegreeTwoThreeSpectrum866.graph sourceMap0443=true := by decide +kernel
theorem fusedMap0443_checked : acceptsGraphIso
    (fused (graph core0443) (root 10) 0 0) DegreeOneSmallSpectrum1033.graph fusedMap0443=true := by decide +kernel
theorem certified0443 : Certified (graph core0443) (root 10) 0 0 :=
  of_native_maps core0443 DegreeTwoThreeSpectrum866.graph DegreeOneSmallSpectrum1033.graph
    sourceMap0443 fusedMap0443 sourceMap0443_checked fusedMap0443_checked
    DegreeTwoThreeFiniteComparisons.comparison0443
#print axioms sourceMap0443_checked
#print axioms fusedMap0443_checked
#print axioms certified0443
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
