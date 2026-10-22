/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5379 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap5379 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 4 4 v)
def fusedMap5379 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 4 4 v)
theorem sourceMap5379_checked : acceptsGraphIso
    (source (graph core5379) (root 5) 4 4) DegreeTwoThreeSpectrum4661.graph sourceMap5379=true := by decide +kernel
theorem fusedMap5379_checked : acceptsGraphIso
    (fused (graph core5379) (root 5) 4 4) DegreeTwoThreeSpectrum3870.graph fusedMap5379=true := by decide +kernel
theorem certified5379 : Certified (graph core5379) (root 5) 4 4 :=
  of_native_maps core5379 DegreeTwoThreeSpectrum4661.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap5379 fusedMap5379 sourceMap5379_checked fusedMap5379_checked
    DegreeTwoThreeFiniteComparisons.comparison5379
#print axioms sourceMap5379_checked
#print axioms fusedMap5379_checked
#print axioms certified5379
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
