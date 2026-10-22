/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5335 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap5335 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4,10,11,12,13,14] (sourceLabel 5 3 4 v)
def fusedMap5335 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 3 4 v)
theorem sourceMap5335_checked : acceptsGraphIso
    (source (graph core5335) (root 5) 3 4) DegreeTwoThreeSpectrum2965.graph sourceMap5335=true := by decide +kernel
theorem fusedMap5335_checked : acceptsGraphIso
    (fused (graph core5335) (root 5) 3 4) DegreeTwoThreeSpectrum2321.graph fusedMap5335=true := by decide +kernel
theorem certified5335 : Certified (graph core5335) (root 5) 3 4 :=
  of_native_maps core5335 DegreeTwoThreeSpectrum2965.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap5335 fusedMap5335 sourceMap5335_checked fusedMap5335_checked
    DegreeTwoThreeFiniteComparisons.comparison5335
#print axioms sourceMap5335_checked
#print axioms fusedMap5335_checked
#print axioms certified5335
def sourceMap5335swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,1,2,3,4] (sourceLabel 5 4 3 v)
def fusedMap5335swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 4 3 v)
theorem sourceMap5335swap_checked : acceptsGraphIso
    (source (graph core5335) (root 5) 4 3) DegreeTwoThreeSpectrum2965.graph sourceMap5335swap=true := by decide +kernel
theorem fusedMap5335swap_checked : acceptsGraphIso
    (fused (graph core5335) (root 5) 4 3) DegreeTwoThreeSpectrum2321.graph fusedMap5335swap=true := by decide +kernel
theorem certified5335swap : Certified (graph core5335) (root 5) 4 3 :=
  of_native_maps core5335 DegreeTwoThreeSpectrum2965.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap5335swap fusedMap5335swap sourceMap5335swap_checked fusedMap5335swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5335
#print axioms sourceMap5335swap_checked
#print axioms fusedMap5335swap_checked
#print axioms certified5335swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
