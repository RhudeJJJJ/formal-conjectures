/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5426 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5426 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 1) → Fin 6 :=
  fun v => ![0,1,2,3,4,5] (sourceLabel 3 0 0 v)
def fusedMap5426 : (Vertices 3 ⊕ Fin 2) → Fin 6 :=
  fun v => ![0,1,2,3,4,5] (fusedLabel 3 0 0 v)
theorem sourceMap5426_checked : acceptsGraphIso
    (source (graph core5426) (root 3) 0 0) DegreeTwoThreeSpectrum005.graph sourceMap5426=true := by decide +kernel
theorem fusedMap5426_checked : acceptsGraphIso
    (fused (graph core5426) (root 3) 0 0) DegreeTwoThreeSpectrum002.graph fusedMap5426=true := by decide +kernel
theorem certified5426 : Certified (graph core5426) (root 3) 0 0 :=
  of_native_maps core5426 DegreeTwoThreeSpectrum005.graph DegreeTwoThreeSpectrum002.graph
    sourceMap5426 fusedMap5426 sourceMap5426_checked fusedMap5426_checked
    DegreeTwoThreeFiniteComparisons.comparison5426
#print axioms sourceMap5426_checked
#print axioms fusedMap5426_checked
#print axioms certified5426
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
