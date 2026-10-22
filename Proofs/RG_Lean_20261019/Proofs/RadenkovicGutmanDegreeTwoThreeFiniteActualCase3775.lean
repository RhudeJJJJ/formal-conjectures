/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3775 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap3775 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,8,6,7,9,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3775 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3775_checked : acceptsGraphIso
    (source (graph core3775) (root 6) 1 4) DegreeTwoThreeSpectrum1788.graph sourceMap3775=true := by decide +kernel
theorem fusedMap3775_checked : acceptsGraphIso
    (fused (graph core3775) (root 6) 1 4) DegreeTwoThreeSpectrum1712.graph fusedMap3775=true := by decide +kernel
theorem certified3775 : Certified (graph core3775) (root 6) 1 4 :=
  of_native_maps core3775 DegreeTwoThreeSpectrum1788.graph DegreeTwoThreeSpectrum1712.graph
    sourceMap3775 fusedMap3775 sourceMap3775_checked fusedMap3775_checked
    DegreeTwoThreeFiniteComparisons.comparison3775
#print axioms sourceMap3775_checked
#print axioms fusedMap3775_checked
#print axioms certified3775
def sourceMap3775swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,12,13,6,7] (sourceLabel 6 4 1 v)
def fusedMap3775swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3775swap_checked : acceptsGraphIso
    (source (graph core3775) (root 6) 4 1) DegreeTwoThreeSpectrum1788.graph sourceMap3775swap=true := by decide +kernel
theorem fusedMap3775swap_checked : acceptsGraphIso
    (fused (graph core3775) (root 6) 4 1) DegreeTwoThreeSpectrum1712.graph fusedMap3775swap=true := by decide +kernel
theorem certified3775swap : Certified (graph core3775) (root 6) 4 1 :=
  of_native_maps core3775 DegreeTwoThreeSpectrum1788.graph DegreeTwoThreeSpectrum1712.graph
    sourceMap3775swap fusedMap3775swap sourceMap3775swap_checked fusedMap3775swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3775
#print axioms sourceMap3775swap_checked
#print axioms fusedMap3775swap_checked
#print axioms certified3775swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
