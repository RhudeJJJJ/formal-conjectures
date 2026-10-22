/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5425 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5425 : (Vertices 2 ⊕ Fin 7 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,15,16,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 2 6 6 v)
def fusedMap5425 : (Vertices 2 ⊕ Fin 14) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 2 6 6 v)
theorem sourceMap5425_checked : acceptsGraphIso
    (source (graph core5425) (root 2) 6 6) DegreeTwoThreeSpectrum5134.graph sourceMap5425=true := by decide +kernel
theorem fusedMap5425_checked : acceptsGraphIso
    (fused (graph core5425) (root 2) 6 6) DegreeTwoThreeSpectrum4959.graph fusedMap5425=true := by decide +kernel
theorem certified5425 : Certified (graph core5425) (root 2) 6 6 :=
  of_native_maps core5425 DegreeTwoThreeSpectrum5134.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap5425 fusedMap5425 sourceMap5425_checked fusedMap5425_checked
    DegreeTwoThreeFiniteComparisons.comparison5425
#print axioms sourceMap5425_checked
#print axioms fusedMap5425_checked
#print axioms certified5425
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
