/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5443 : Family 7 := level7.get ⟨69,by decide⟩
def sourceMap5443 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap5443 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap5443_checked : acceptsGraphIso
    (source (graph core5443) (root 7) 0 0) DegreeTwoThreeSpectrum141.graph sourceMap5443=true := by decide +kernel
theorem fusedMap5443_checked : acceptsGraphIso
    (fused (graph core5443) (root 7) 0 0) DegreeTwoThreeSpectrum099.graph fusedMap5443=true := by decide +kernel
theorem certified5443 : Certified (graph core5443) (root 7) 0 0 :=
  of_native_maps core5443 DegreeTwoThreeSpectrum141.graph DegreeTwoThreeSpectrum099.graph
    sourceMap5443 fusedMap5443 sourceMap5443_checked fusedMap5443_checked
    DegreeTwoThreeFiniteComparisons.comparison5443
#print axioms sourceMap5443_checked
#print axioms fusedMap5443_checked
#print axioms certified5443
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
