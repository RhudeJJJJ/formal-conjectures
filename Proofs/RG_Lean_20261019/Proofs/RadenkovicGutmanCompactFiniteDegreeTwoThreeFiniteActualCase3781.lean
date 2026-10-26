/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3781 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap3781 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3781 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3781_checked : acceptsGraphIso
    (source (graph core3781) (root 6) 1 4) DegreeTwoThreeSpectrum2049.graph sourceMap3781=true := by decide +kernel
theorem fusedMap3781_checked : acceptsGraphIso
    (fused (graph core3781) (root 6) 1 4) DegreeTwoThreeSpectrum1779.graph fusedMap3781=true := by decide +kernel
theorem certified3781 : Certified (graph core3781) (root 6) 1 4 :=
  of_native_maps core3781 DegreeTwoThreeSpectrum2049.graph DegreeTwoThreeSpectrum1779.graph
    sourceMap3781 fusedMap3781 sourceMap3781_checked fusedMap3781_checked
    DegreeTwoThreeFiniteComparisons.comparison3781
#print axioms sourceMap3781_checked
#print axioms fusedMap3781_checked
#print axioms certified3781
def sourceMap3781swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,8,9] (sourceLabel 6 4 1 v)
def fusedMap3781swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3781swap_checked : acceptsGraphIso
    (source (graph core3781) (root 6) 4 1) DegreeTwoThreeSpectrum2049.graph sourceMap3781swap=true := by decide +kernel
theorem fusedMap3781swap_checked : acceptsGraphIso
    (fused (graph core3781) (root 6) 4 1) DegreeTwoThreeSpectrum1779.graph fusedMap3781swap=true := by decide +kernel
theorem certified3781swap : Certified (graph core3781) (root 6) 4 1 :=
  of_native_maps core3781 DegreeTwoThreeSpectrum2049.graph DegreeTwoThreeSpectrum1779.graph
    sourceMap3781swap fusedMap3781swap sourceMap3781swap_checked fusedMap3781swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3781
#print axioms sourceMap3781swap_checked
#print axioms fusedMap3781swap_checked
#print axioms certified3781swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
