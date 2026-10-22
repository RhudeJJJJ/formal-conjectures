/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5417 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5417 : (Vertices 2 ⊕ Fin 6 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,13,14,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 2 5 5 v)
def fusedMap5417 : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 5 5 v)
theorem sourceMap5417_checked : acceptsGraphIso
    (source (graph core5417) (root 2) 5 5) DegreeTwoThreeSpectrum2436.graph sourceMap5417=true := by decide +kernel
theorem fusedMap5417_checked : acceptsGraphIso
    (fused (graph core5417) (root 2) 5 5) DegreeTwoThreeSpectrum2309.graph fusedMap5417=true := by decide +kernel
theorem certified5417 : Certified (graph core5417) (root 2) 5 5 :=
  of_native_maps core5417 DegreeTwoThreeSpectrum2436.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap5417 fusedMap5417 sourceMap5417_checked fusedMap5417_checked
    DegreeTwoThreeFiniteComparisons.comparison5417
#print axioms sourceMap5417_checked
#print axioms fusedMap5417_checked
#print axioms certified5417
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
