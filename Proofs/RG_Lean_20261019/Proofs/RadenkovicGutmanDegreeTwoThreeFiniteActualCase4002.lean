/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4002 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap4002 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap4002 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap4002_checked : acceptsGraphIso
    (source (graph core4002) (root 6) 1 6) DegreeTwoThreeSpectrum4125.graph sourceMap4002=true := by decide +kernel
theorem fusedMap4002_checked : acceptsGraphIso
    (fused (graph core4002) (root 6) 1 6) DegreeTwoThreeSpectrum3877.graph fusedMap4002=true := by decide +kernel
theorem certified4002 : Certified (graph core4002) (root 6) 1 6 :=
  of_native_maps core4002 DegreeTwoThreeSpectrum4125.graph DegreeTwoThreeSpectrum3877.graph
    sourceMap4002 fusedMap4002 sourceMap4002_checked fusedMap4002_checked
    DegreeTwoThreeFiniteComparisons.comparison4002
#print axioms sourceMap4002_checked
#print axioms fusedMap4002_checked
#print axioms certified4002
def sourceMap4002swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,14,15,8,9] (sourceLabel 6 6 1 v)
def fusedMap4002swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap4002swap_checked : acceptsGraphIso
    (source (graph core4002) (root 6) 6 1) DegreeTwoThreeSpectrum4125.graph sourceMap4002swap=true := by decide +kernel
theorem fusedMap4002swap_checked : acceptsGraphIso
    (fused (graph core4002) (root 6) 6 1) DegreeTwoThreeSpectrum3877.graph fusedMap4002swap=true := by decide +kernel
theorem certified4002swap : Certified (graph core4002) (root 6) 6 1 :=
  of_native_maps core4002 DegreeTwoThreeSpectrum4125.graph DegreeTwoThreeSpectrum3877.graph
    sourceMap4002swap fusedMap4002swap sourceMap4002swap_checked fusedMap4002swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4002
#print axioms sourceMap4002swap_checked
#print axioms fusedMap4002swap_checked
#print axioms certified4002swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
