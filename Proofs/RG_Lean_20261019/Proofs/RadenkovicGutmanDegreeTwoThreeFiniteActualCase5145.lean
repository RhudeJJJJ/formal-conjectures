/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5145 : Family 8 := level8.get ⟨98,by decide⟩
def sourceMap5145 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5145 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5145_checked : acceptsGraphIso
    (source (graph core5145) (root 8) 2 4) DegreeTwoThreeSpectrum6037.graph sourceMap5145=true := by decide +kernel
theorem fusedMap5145_checked : acceptsGraphIso
    (fused (graph core5145) (root 8) 2 4) DegreeTwoThreeSpectrum5153.graph fusedMap5145=true := by decide +kernel
theorem certified5145 : Certified (graph core5145) (root 8) 2 4 :=
  of_native_maps core5145 DegreeTwoThreeSpectrum6037.graph DegreeTwoThreeSpectrum5153.graph
    sourceMap5145 fusedMap5145 sourceMap5145_checked fusedMap5145_checked
    DegreeTwoThreeFiniteComparisons.comparison5145
#print axioms sourceMap5145_checked
#print axioms fusedMap5145_checked
#print axioms certified5145
def sourceMap5145swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5145swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5145swap_checked : acceptsGraphIso
    (source (graph core5145) (root 8) 4 2) DegreeTwoThreeSpectrum6037.graph sourceMap5145swap=true := by decide +kernel
theorem fusedMap5145swap_checked : acceptsGraphIso
    (fused (graph core5145) (root 8) 4 2) DegreeTwoThreeSpectrum5153.graph fusedMap5145swap=true := by decide +kernel
theorem certified5145swap : Certified (graph core5145) (root 8) 4 2 :=
  of_native_maps core5145 DegreeTwoThreeSpectrum6037.graph DegreeTwoThreeSpectrum5153.graph
    sourceMap5145swap fusedMap5145swap sourceMap5145swap_checked fusedMap5145swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5145
#print axioms sourceMap5145swap_checked
#print axioms fusedMap5145swap_checked
#print axioms certified5145swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
