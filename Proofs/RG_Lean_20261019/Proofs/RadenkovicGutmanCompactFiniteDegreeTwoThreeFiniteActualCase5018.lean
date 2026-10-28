/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5018 : Family 10 := level10.get ⟨1662,by decide⟩
def sourceMap5018 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5018 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5018_checked : acceptsGraphIso
    (source (graph core5018) (root 10) 2 2) DegreeTwoThreeSpectrum7619.graph sourceMap5018=true := by decide +kernel
theorem fusedMap5018_checked : acceptsGraphIso
    (fused (graph core5018) (root 10) 2 2) DegreeTwoThreeSpectrum6278.graph fusedMap5018=true := by decide +kernel
theorem certified5018 : Certified (graph core5018) (root 10) 2 2 :=
  of_native_maps core5018 DegreeTwoThreeSpectrum7619.graph DegreeTwoThreeSpectrum6278.graph
    sourceMap5018 fusedMap5018 sourceMap5018_checked fusedMap5018_checked
    DegreeTwoThreeFiniteComparisons.comparison5018
#print axioms sourceMap5018_checked
#print axioms fusedMap5018_checked
#print axioms certified5018
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
