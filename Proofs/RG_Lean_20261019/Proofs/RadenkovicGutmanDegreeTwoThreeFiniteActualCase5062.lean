/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5062 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap5062 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,9,6,7,8,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap5062 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap5062_checked : acceptsGraphIso
    (source (graph core5062) (root 5) 2 4) DegreeTwoThreeSpectrum2143.graph sourceMap5062=true := by decide +kernel
theorem fusedMap5062_checked : acceptsGraphIso
    (fused (graph core5062) (root 5) 2 4) DegreeTwoThreeSpectrum1718.graph fusedMap5062=true := by decide +kernel
theorem certified5062 : Certified (graph core5062) (root 5) 2 4 :=
  of_native_maps core5062 DegreeTwoThreeSpectrum2143.graph DegreeTwoThreeSpectrum1718.graph
    sourceMap5062 fusedMap5062 sourceMap5062_checked fusedMap5062_checked
    DegreeTwoThreeFiniteComparisons.comparison5062
#print axioms sourceMap5062_checked
#print axioms fusedMap5062_checked
#print axioms certified5062
def sourceMap5062swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,2,3,4,5,9,0,10,11,12,13,6,7,8] (sourceLabel 5 4 2 v)
def fusedMap5062swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap5062swap_checked : acceptsGraphIso
    (source (graph core5062) (root 5) 4 2) DegreeTwoThreeSpectrum2143.graph sourceMap5062swap=true := by decide +kernel
theorem fusedMap5062swap_checked : acceptsGraphIso
    (fused (graph core5062) (root 5) 4 2) DegreeTwoThreeSpectrum1718.graph fusedMap5062swap=true := by decide +kernel
theorem certified5062swap : Certified (graph core5062) (root 5) 4 2 :=
  of_native_maps core5062 DegreeTwoThreeSpectrum2143.graph DegreeTwoThreeSpectrum1718.graph
    sourceMap5062swap fusedMap5062swap sourceMap5062swap_checked fusedMap5062swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5062
#print axioms sourceMap5062swap_checked
#print axioms fusedMap5062swap_checked
#print axioms certified5062swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
