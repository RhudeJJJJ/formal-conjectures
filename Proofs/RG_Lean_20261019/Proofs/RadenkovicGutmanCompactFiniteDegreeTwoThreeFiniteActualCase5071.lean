/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5071 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap5071 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5071 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5071_checked : acceptsGraphIso
    (source (graph core5071) (root 6) 2 4) DegreeTwoThreeSpectrum3119.graph sourceMap5071=true := by decide +kernel
theorem fusedMap5071_checked : acceptsGraphIso
    (fused (graph core5071) (root 6) 2 4) DegreeTwoThreeSpectrum2316.graph fusedMap5071=true := by decide +kernel
theorem certified5071 : Certified (graph core5071) (root 6) 2 4 :=
  of_native_maps core5071 DegreeTwoThreeSpectrum3119.graph DegreeTwoThreeSpectrum2316.graph
    sourceMap5071 fusedMap5071 sourceMap5071_checked fusedMap5071_checked
    DegreeTwoThreeFiniteComparisons.comparison5071
#print axioms sourceMap5071_checked
#print axioms fusedMap5071_checked
#print axioms certified5071
def sourceMap5071swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap5071swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5071swap_checked : acceptsGraphIso
    (source (graph core5071) (root 6) 4 2) DegreeTwoThreeSpectrum3119.graph sourceMap5071swap=true := by decide +kernel
theorem fusedMap5071swap_checked : acceptsGraphIso
    (fused (graph core5071) (root 6) 4 2) DegreeTwoThreeSpectrum2316.graph fusedMap5071swap=true := by decide +kernel
theorem certified5071swap : Certified (graph core5071) (root 6) 4 2 :=
  of_native_maps core5071 DegreeTwoThreeSpectrum3119.graph DegreeTwoThreeSpectrum2316.graph
    sourceMap5071swap fusedMap5071swap sourceMap5071swap_checked fusedMap5071swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5071
#print axioms sourceMap5071swap_checked
#print axioms fusedMap5071swap_checked
#print axioms certified5071swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
