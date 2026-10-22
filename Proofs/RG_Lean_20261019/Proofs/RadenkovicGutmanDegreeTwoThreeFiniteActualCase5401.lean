/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5401 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5401 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5,10,11,12,13,14,15] (sourceLabel 4 4 5 v)
def fusedMap5401 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 4 5 v)
theorem sourceMap5401_checked : acceptsGraphIso
    (source (graph core5401) (root 4) 4 5) DegreeTwoThreeSpectrum4156.graph sourceMap5401=true := by decide +kernel
theorem fusedMap5401_checked : acceptsGraphIso
    (fused (graph core5401) (root 4) 4 5) DegreeTwoThreeSpectrum3855.graph fusedMap5401=true := by decide +kernel
theorem certified5401 : Certified (graph core5401) (root 4) 4 5 :=
  of_native_maps core5401 DegreeTwoThreeSpectrum4156.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap5401 fusedMap5401 sourceMap5401_checked fusedMap5401_checked
    DegreeTwoThreeFiniteComparisons.comparison5401
#print axioms sourceMap5401_checked
#print axioms fusedMap5401_checked
#print axioms certified5401
def sourceMap5401swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,15,1,2,3,4,5] (sourceLabel 4 5 4 v)
def fusedMap5401swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 5 4 v)
theorem sourceMap5401swap_checked : acceptsGraphIso
    (source (graph core5401) (root 4) 5 4) DegreeTwoThreeSpectrum4156.graph sourceMap5401swap=true := by decide +kernel
theorem fusedMap5401swap_checked : acceptsGraphIso
    (fused (graph core5401) (root 4) 5 4) DegreeTwoThreeSpectrum3855.graph fusedMap5401swap=true := by decide +kernel
theorem certified5401swap : Certified (graph core5401) (root 4) 5 4 :=
  of_native_maps core5401 DegreeTwoThreeSpectrum4156.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap5401swap fusedMap5401swap sourceMap5401swap_checked fusedMap5401swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5401
#print axioms sourceMap5401swap_checked
#print axioms fusedMap5401swap_checked
#print axioms certified5401swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
