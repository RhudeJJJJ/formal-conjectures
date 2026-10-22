/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5329 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5329 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,5,6,7,8,1,2,3,4,9,10,11,12,13] (sourceLabel 4 3 4 v)
def fusedMap5329 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 3 4 v)
theorem sourceMap5329_checked : acceptsGraphIso
    (source (graph core5329) (root 4) 3 4) DegreeTwoThreeSpectrum1912.graph sourceMap5329=true := by decide +kernel
theorem fusedMap5329_checked : acceptsGraphIso
    (fused (graph core5329) (root 4) 3 4) DegreeTwoThreeSpectrum1716.graph fusedMap5329=true := by decide +kernel
theorem certified5329 : Certified (graph core5329) (root 4) 3 4 :=
  of_native_maps core5329 DegreeTwoThreeSpectrum1912.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap5329 fusedMap5329 sourceMap5329_checked fusedMap5329_checked
    DegreeTwoThreeFiniteComparisons.comparison5329
#print axioms sourceMap5329_checked
#print axioms fusedMap5329_checked
#print axioms certified5329
def sourceMap5329swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,1,2,3,4] (sourceLabel 4 4 3 v)
def fusedMap5329swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 4 3 v)
theorem sourceMap5329swap_checked : acceptsGraphIso
    (source (graph core5329) (root 4) 4 3) DegreeTwoThreeSpectrum1912.graph sourceMap5329swap=true := by decide +kernel
theorem fusedMap5329swap_checked : acceptsGraphIso
    (fused (graph core5329) (root 4) 4 3) DegreeTwoThreeSpectrum1716.graph fusedMap5329swap=true := by decide +kernel
theorem certified5329swap : Certified (graph core5329) (root 4) 4 3 :=
  of_native_maps core5329 DegreeTwoThreeSpectrum1912.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap5329swap fusedMap5329swap sourceMap5329swap_checked fusedMap5329swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5329
#print axioms sourceMap5329swap_checked
#print axioms fusedMap5329swap_checked
#print axioms certified5329swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
