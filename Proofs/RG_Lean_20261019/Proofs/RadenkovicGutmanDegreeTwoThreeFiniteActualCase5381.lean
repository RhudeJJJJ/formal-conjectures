/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5381 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap5381 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 4 4 v)
def fusedMap5381 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 4 4 v)
theorem sourceMap5381_checked : acceptsGraphIso
    (source (graph core5381) (root 5) 4 4) DegreeTwoThreeSpectrum4663.graph sourceMap5381=true := by decide +kernel
theorem fusedMap5381_checked : acceptsGraphIso
    (fused (graph core5381) (root 5) 4 4) DegreeTwoThreeSpectrum3922.graph fusedMap5381=true := by decide +kernel
theorem certified5381 : Certified (graph core5381) (root 5) 4 4 :=
  of_native_maps core5381 DegreeTwoThreeSpectrum4663.graph DegreeTwoThreeSpectrum3922.graph
    sourceMap5381 fusedMap5381 sourceMap5381_checked fusedMap5381_checked
    DegreeTwoThreeFiniteComparisons.comparison5381
#print axioms sourceMap5381_checked
#print axioms fusedMap5381_checked
#print axioms certified5381
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
