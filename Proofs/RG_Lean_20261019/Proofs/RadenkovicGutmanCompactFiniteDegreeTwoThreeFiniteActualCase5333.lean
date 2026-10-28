/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5333 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap5333 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4,10,11,12,13,14] (sourceLabel 5 3 4 v)
def fusedMap5333 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 3 4 v)
theorem sourceMap5333_checked : acceptsGraphIso
    (source (graph core5333) (root 5) 3 4) DegreeTwoThreeSpectrum2954.graph sourceMap5333=true := by decide +kernel
theorem fusedMap5333_checked : acceptsGraphIso
    (fused (graph core5333) (root 5) 3 4) DegreeTwoThreeSpectrum2387.graph fusedMap5333=true := by decide +kernel
theorem certified5333 : Certified (graph core5333) (root 5) 3 4 :=
  of_native_maps core5333 DegreeTwoThreeSpectrum2954.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap5333 fusedMap5333 sourceMap5333_checked fusedMap5333_checked
    DegreeTwoThreeFiniteComparisons.comparison5333
#print axioms sourceMap5333_checked
#print axioms fusedMap5333_checked
#print axioms certified5333
def sourceMap5333swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,1,2,3,4] (sourceLabel 5 4 3 v)
def fusedMap5333swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 4 3 v)
theorem sourceMap5333swap_checked : acceptsGraphIso
    (source (graph core5333) (root 5) 4 3) DegreeTwoThreeSpectrum2954.graph sourceMap5333swap=true := by decide +kernel
theorem fusedMap5333swap_checked : acceptsGraphIso
    (fused (graph core5333) (root 5) 4 3) DegreeTwoThreeSpectrum2387.graph fusedMap5333swap=true := by decide +kernel
theorem certified5333swap : Certified (graph core5333) (root 5) 4 3 :=
  of_native_maps core5333 DegreeTwoThreeSpectrum2954.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap5333swap fusedMap5333swap sourceMap5333swap_checked fusedMap5333swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5333
#print axioms sourceMap5333swap_checked
#print axioms fusedMap5333swap_checked
#print axioms certified5333swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
