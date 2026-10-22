/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4025 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap4025 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,6,7,4,5,2,1,0,8,9,10,11,12,13] (sourceLabel 2 1 8 v)
def fusedMap4025 : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 1 8 v)
theorem sourceMap4025_checked : acceptsGraphIso
    (source (graph core4025) (root 2) 1 8) DegreeTwoThreeSpectrum1717.graph sourceMap4025=true := by decide +kernel
theorem fusedMap4025_checked : acceptsGraphIso
    (fused (graph core4025) (root 2) 1 8) DegreeTwoThreeSpectrum1715.graph fusedMap4025=true := by decide +kernel
theorem certified4025 : Certified (graph core4025) (root 2) 1 8 :=
  of_native_maps core4025 DegreeTwoThreeSpectrum1717.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap4025 fusedMap4025 sourceMap4025_checked fusedMap4025_checked
    DegreeTwoThreeFiniteComparisons.comparison4025
#print axioms sourceMap4025_checked
#print axioms fusedMap4025_checked
#print axioms certified4025
def sourceMap4025swap : (Vertices 2 ⊕ Fin 9 ⊕ Fin 2) → Fin 14 :=
  fun v => ![3,6,7,2,1,0,8,9,10,11,12,13,4,5] (sourceLabel 2 8 1 v)
def fusedMap4025swap : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 8 1 v)
theorem sourceMap4025swap_checked : acceptsGraphIso
    (source (graph core4025) (root 2) 8 1) DegreeTwoThreeSpectrum1717.graph sourceMap4025swap=true := by decide +kernel
theorem fusedMap4025swap_checked : acceptsGraphIso
    (fused (graph core4025) (root 2) 8 1) DegreeTwoThreeSpectrum1715.graph fusedMap4025swap=true := by decide +kernel
theorem certified4025swap : Certified (graph core4025) (root 2) 8 1 :=
  of_native_maps core4025 DegreeTwoThreeSpectrum1717.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap4025swap fusedMap4025swap sourceMap4025swap_checked fusedMap4025swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4025
#print axioms sourceMap4025swap_checked
#print axioms fusedMap4025swap_checked
#print axioms certified4025swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
