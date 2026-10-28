/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5420 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5420 : (Vertices 4 ⊕ Fin 6 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 4 5 5 v)
def fusedMap5420 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 5 5 v)
theorem sourceMap5420_checked : acceptsGraphIso
    (source (graph core5420) (root 4) 5 5) DegreeTwoThreeSpectrum5958.graph sourceMap5420=true := by decide +kernel
theorem fusedMap5420_checked : acceptsGraphIso
    (fused (graph core5420) (root 4) 5 5) DegreeTwoThreeSpectrum4980.graph fusedMap5420=true := by decide +kernel
theorem certified5420 : Certified (graph core5420) (root 4) 5 5 :=
  of_native_maps core5420 DegreeTwoThreeSpectrum5958.graph DegreeTwoThreeSpectrum4980.graph
    sourceMap5420 fusedMap5420 sourceMap5420_checked fusedMap5420_checked
    DegreeTwoThreeFiniteComparisons.comparison5420
#print axioms sourceMap5420_checked
#print axioms fusedMap5420_checked
#print axioms certified5420
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
