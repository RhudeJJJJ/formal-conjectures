/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5331 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap5331 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4,10,11,12,13,14] (sourceLabel 5 3 4 v)
def fusedMap5331 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 3 4 v)
theorem sourceMap5331_checked : acceptsGraphIso
    (source (graph core5331) (root 5) 3 4) DegreeTwoThreeSpectrum2946.graph sourceMap5331=true := by decide +kernel
theorem fusedMap5331_checked : acceptsGraphIso
    (fused (graph core5331) (root 5) 3 4) DegreeTwoThreeSpectrum2333.graph fusedMap5331=true := by decide +kernel
theorem certified5331 : Certified (graph core5331) (root 5) 3 4 :=
  of_native_maps core5331 DegreeTwoThreeSpectrum2946.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap5331 fusedMap5331 sourceMap5331_checked fusedMap5331_checked
    DegreeTwoThreeFiniteComparisons.comparison5331
#print axioms sourceMap5331_checked
#print axioms fusedMap5331_checked
#print axioms certified5331
def sourceMap5331swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,1,2,3,4] (sourceLabel 5 4 3 v)
def fusedMap5331swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 4 3 v)
theorem sourceMap5331swap_checked : acceptsGraphIso
    (source (graph core5331) (root 5) 4 3) DegreeTwoThreeSpectrum2946.graph sourceMap5331swap=true := by decide +kernel
theorem fusedMap5331swap_checked : acceptsGraphIso
    (fused (graph core5331) (root 5) 4 3) DegreeTwoThreeSpectrum2333.graph fusedMap5331swap=true := by decide +kernel
theorem certified5331swap : Certified (graph core5331) (root 5) 4 3 :=
  of_native_maps core5331 DegreeTwoThreeSpectrum2946.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap5331swap fusedMap5331swap sourceMap5331swap_checked fusedMap5331swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5331
#print axioms sourceMap5331swap_checked
#print axioms fusedMap5331swap_checked
#print axioms certified5331swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
