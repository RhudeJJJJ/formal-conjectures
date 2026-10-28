/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5004 : Family 10 := level10.get ⟨1631,by decide⟩
def sourceMap5004 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap5004 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5004_checked : acceptsGraphIso
    (source (graph core5004) (root 10) 2 2) DegreeTwoThreeSpectrum7605.graph sourceMap5004=true := by decide +kernel
theorem fusedMap5004_checked : acceptsGraphIso
    (fused (graph core5004) (root 10) 2 2) DegreeTwoThreeSpectrum6196.graph fusedMap5004=true := by decide +kernel
theorem certified5004 : Certified (graph core5004) (root 10) 2 2 :=
  of_native_maps core5004 DegreeTwoThreeSpectrum7605.graph DegreeTwoThreeSpectrum6196.graph
    sourceMap5004 fusedMap5004 sourceMap5004_checked fusedMap5004_checked
    DegreeTwoThreeFiniteComparisons.comparison5004
#print axioms sourceMap5004_checked
#print axioms fusedMap5004_checked
#print axioms certified5004
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
