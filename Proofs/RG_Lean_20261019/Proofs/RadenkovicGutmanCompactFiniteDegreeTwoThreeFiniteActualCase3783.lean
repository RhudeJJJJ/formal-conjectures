/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3783 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap3783 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3783 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3783_checked : acceptsGraphIso
    (source (graph core3783) (root 6) 1 4) DegreeTwoThreeSpectrum2127.graph sourceMap3783=true := by decide +kernel
theorem fusedMap3783_checked : acceptsGraphIso
    (fused (graph core3783) (root 6) 1 4) DegreeTwoThreeSpectrum1823.graph fusedMap3783=true := by decide +kernel
theorem certified3783 : Certified (graph core3783) (root 6) 1 4 :=
  of_native_maps core3783 DegreeTwoThreeSpectrum2127.graph DegreeTwoThreeSpectrum1823.graph
    sourceMap3783 fusedMap3783 sourceMap3783_checked fusedMap3783_checked
    DegreeTwoThreeFiniteComparisons.comparison3783
#print axioms sourceMap3783_checked
#print axioms fusedMap3783_checked
#print axioms certified3783
def sourceMap3783swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,7,8] (sourceLabel 6 4 1 v)
def fusedMap3783swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3783swap_checked : acceptsGraphIso
    (source (graph core3783) (root 6) 4 1) DegreeTwoThreeSpectrum2127.graph sourceMap3783swap=true := by decide +kernel
theorem fusedMap3783swap_checked : acceptsGraphIso
    (fused (graph core3783) (root 6) 4 1) DegreeTwoThreeSpectrum1823.graph fusedMap3783swap=true := by decide +kernel
theorem certified3783swap : Certified (graph core3783) (root 6) 4 1 :=
  of_native_maps core3783 DegreeTwoThreeSpectrum2127.graph DegreeTwoThreeSpectrum1823.graph
    sourceMap3783swap fusedMap3783swap sourceMap3783swap_checked fusedMap3783swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3783
#print axioms sourceMap3783swap_checked
#print axioms fusedMap3783swap_checked
#print axioms certified3783swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
