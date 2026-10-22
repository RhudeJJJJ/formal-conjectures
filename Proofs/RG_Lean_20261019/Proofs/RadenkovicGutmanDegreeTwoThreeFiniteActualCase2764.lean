/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2764 : Family 10 := level10.get ⟨977,by decide⟩
def sourceMap2764 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,16,6,7,8,9,10] (sourceLabel 10 0 4 v)
def fusedMap2764 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2764_checked : acceptsGraphIso
    (source (graph core2764) (root 10) 0 4) DegreeTwoThreeSpectrum7043.graph sourceMap2764=true := by decide +kernel
theorem fusedMap2764_checked : acceptsGraphIso
    (fused (graph core2764) (root 10) 0 4) DegreeTwoThreeSpectrum5911.graph fusedMap2764=true := by decide +kernel
theorem certified2764 : Certified (graph core2764) (root 10) 0 4 :=
  of_native_maps core2764 DegreeTwoThreeSpectrum7043.graph DegreeTwoThreeSpectrum5911.graph
    sourceMap2764 fusedMap2764 sourceMap2764_checked fusedMap2764_checked
    DegreeTwoThreeFiniteComparisons.comparison2764
#print axioms sourceMap2764_checked
#print axioms fusedMap2764_checked
#print axioms certified2764
def sourceMap2764swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10,16] (sourceLabel 10 4 0 v)
def fusedMap2764swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2764swap_checked : acceptsGraphIso
    (source (graph core2764) (root 10) 4 0) DegreeTwoThreeSpectrum7043.graph sourceMap2764swap=true := by decide +kernel
theorem fusedMap2764swap_checked : acceptsGraphIso
    (fused (graph core2764) (root 10) 4 0) DegreeTwoThreeSpectrum5911.graph fusedMap2764swap=true := by decide +kernel
theorem certified2764swap : Certified (graph core2764) (root 10) 4 0 :=
  of_native_maps core2764 DegreeTwoThreeSpectrum7043.graph DegreeTwoThreeSpectrum5911.graph
    sourceMap2764swap fusedMap2764swap sourceMap2764swap_checked fusedMap2764swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2764
#print axioms sourceMap2764swap_checked
#print axioms fusedMap2764swap_checked
#print axioms certified2764swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
