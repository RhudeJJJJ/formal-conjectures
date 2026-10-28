/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5383 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap5383 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5383 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5383_checked : acceptsGraphIso
    (source (graph core5383) (root 6) 4 4) DegreeTwoThreeSpectrum7042.graph sourceMap5383=true := by decide +kernel
theorem fusedMap5383_checked : acceptsGraphIso
    (fused (graph core5383) (root 6) 4 4) DegreeTwoThreeSpectrum4993.graph fusedMap5383=true := by decide +kernel
theorem certified5383 : Certified (graph core5383) (root 6) 4 4 :=
  of_native_maps core5383 DegreeTwoThreeSpectrum7042.graph DegreeTwoThreeSpectrum4993.graph
    sourceMap5383 fusedMap5383 sourceMap5383_checked fusedMap5383_checked
    DegreeTwoThreeFiniteComparisons.comparison5383
#print axioms sourceMap5383_checked
#print axioms fusedMap5383_checked
#print axioms certified5383
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
