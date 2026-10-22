/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5069 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap5069 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5069 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5069_checked : acceptsGraphIso
    (source (graph core5069) (root 6) 2 4) DegreeTwoThreeSpectrum2911.graph sourceMap5069=true := by decide +kernel
theorem fusedMap5069_checked : acceptsGraphIso
    (fused (graph core5069) (root 6) 2 4) DegreeTwoThreeSpectrum2398.graph fusedMap5069=true := by decide +kernel
theorem certified5069 : Certified (graph core5069) (root 6) 2 4 :=
  of_native_maps core5069 DegreeTwoThreeSpectrum2911.graph DegreeTwoThreeSpectrum2398.graph
    sourceMap5069 fusedMap5069 sourceMap5069_checked fusedMap5069_checked
    DegreeTwoThreeFiniteComparisons.comparison5069
#print axioms sourceMap5069_checked
#print axioms fusedMap5069_checked
#print axioms certified5069
def sourceMap5069swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,6,7,8] (sourceLabel 6 4 2 v)
def fusedMap5069swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5069swap_checked : acceptsGraphIso
    (source (graph core5069) (root 6) 4 2) DegreeTwoThreeSpectrum2911.graph sourceMap5069swap=true := by decide +kernel
theorem fusedMap5069swap_checked : acceptsGraphIso
    (fused (graph core5069) (root 6) 4 2) DegreeTwoThreeSpectrum2398.graph fusedMap5069swap=true := by decide +kernel
theorem certified5069swap : Certified (graph core5069) (root 6) 4 2 :=
  of_native_maps core5069 DegreeTwoThreeSpectrum2911.graph DegreeTwoThreeSpectrum2398.graph
    sourceMap5069swap fusedMap5069swap sourceMap5069swap_checked fusedMap5069swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5069
#print axioms sourceMap5069swap_checked
#print axioms fusedMap5069swap_checked
#print axioms certified5069swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
