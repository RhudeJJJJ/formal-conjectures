/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3857 : Family 8 := level8.get ⟨111,by decide⟩
def sourceMap3857 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3857 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3857_checked : acceptsGraphIso
    (source (graph core3857) (root 8) 1 4) DegreeTwoThreeSpectrum4282.graph sourceMap3857=true := by decide +kernel
theorem fusedMap3857_checked : acceptsGraphIso
    (fused (graph core3857) (root 8) 1 4) DegreeTwoThreeSpectrum3920.graph fusedMap3857=true := by decide +kernel
theorem certified3857 : Certified (graph core3857) (root 8) 1 4 :=
  of_native_maps core3857 DegreeTwoThreeSpectrum4282.graph DegreeTwoThreeSpectrum3920.graph
    sourceMap3857 fusedMap3857 sourceMap3857_checked fusedMap3857_checked
    DegreeTwoThreeFiniteComparisons.comparison3857
#print axioms sourceMap3857_checked
#print axioms fusedMap3857_checked
#print axioms certified3857
def sourceMap3857swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3857swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3857swap_checked : acceptsGraphIso
    (source (graph core3857) (root 8) 4 1) DegreeTwoThreeSpectrum4282.graph sourceMap3857swap=true := by decide +kernel
theorem fusedMap3857swap_checked : acceptsGraphIso
    (fused (graph core3857) (root 8) 4 1) DegreeTwoThreeSpectrum3920.graph fusedMap3857swap=true := by decide +kernel
theorem certified3857swap : Certified (graph core3857) (root 8) 4 1 :=
  of_native_maps core3857 DegreeTwoThreeSpectrum4282.graph DegreeTwoThreeSpectrum3920.graph
    sourceMap3857swap fusedMap3857swap sourceMap3857swap_checked fusedMap3857swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3857
#print axioms sourceMap3857swap_checked
#print axioms fusedMap3857swap_checked
#print axioms certified3857swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
