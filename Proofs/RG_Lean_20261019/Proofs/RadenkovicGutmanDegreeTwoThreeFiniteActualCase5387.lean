/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5387 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap5387 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 4 4 v)
def fusedMap5387 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5387_checked : acceptsGraphIso
    (source (graph core5387) (root 6) 4 4) DegreeTwoThreeSpectrum7046.graph sourceMap5387=true := by decide +kernel
theorem fusedMap5387_checked : acceptsGraphIso
    (fused (graph core5387) (root 6) 4 4) DegreeTwoThreeSpectrum4967.graph fusedMap5387=true := by decide +kernel
theorem certified5387 : Certified (graph core5387) (root 6) 4 4 :=
  of_native_maps core5387 DegreeTwoThreeSpectrum7046.graph DegreeTwoThreeSpectrum4967.graph
    sourceMap5387 fusedMap5387 sourceMap5387_checked fusedMap5387_checked
    DegreeTwoThreeFiniteComparisons.comparison5387
#print axioms sourceMap5387_checked
#print axioms fusedMap5387_checked
#print axioms certified5387
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
