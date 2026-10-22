/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4015 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap4015 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,8,6,7,2,1,0,9,10,11,12,13] (sourceLabel 3 1 7 v)
def fusedMap4015 : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 1 7 v)
theorem sourceMap4015_checked : acceptsGraphIso
    (source (graph core4015) (root 3) 1 7) DegreeTwoThreeSpectrum1807.graph sourceMap4015=true := by decide +kernel
theorem fusedMap4015_checked : acceptsGraphIso
    (fused (graph core4015) (root 3) 1 7) DegreeTwoThreeSpectrum1722.graph fusedMap4015=true := by decide +kernel
theorem certified4015 : Certified (graph core4015) (root 3) 1 7 :=
  of_native_maps core4015 DegreeTwoThreeSpectrum1807.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap4015 fusedMap4015 sourceMap4015_checked fusedMap4015_checked
    DegreeTwoThreeFiniteComparisons.comparison4015
#print axioms sourceMap4015_checked
#print axioms fusedMap4015_checked
#print axioms certified4015
def sourceMap4015swap : (Vertices 3 ⊕ Fin 8 ⊕ Fin 2) → Fin 14 :=
  fun v => ![3,4,5,8,2,1,0,9,10,11,12,13,6,7] (sourceLabel 3 7 1 v)
def fusedMap4015swap : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 7 1 v)
theorem sourceMap4015swap_checked : acceptsGraphIso
    (source (graph core4015) (root 3) 7 1) DegreeTwoThreeSpectrum1807.graph sourceMap4015swap=true := by decide +kernel
theorem fusedMap4015swap_checked : acceptsGraphIso
    (fused (graph core4015) (root 3) 7 1) DegreeTwoThreeSpectrum1722.graph fusedMap4015swap=true := by decide +kernel
theorem certified4015swap : Certified (graph core4015) (root 3) 7 1 :=
  of_native_maps core4015 DegreeTwoThreeSpectrum1807.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap4015swap fusedMap4015swap sourceMap4015swap_checked fusedMap4015swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4015
#print axioms sourceMap4015swap_checked
#print axioms fusedMap4015swap_checked
#print axioms certified4015swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
