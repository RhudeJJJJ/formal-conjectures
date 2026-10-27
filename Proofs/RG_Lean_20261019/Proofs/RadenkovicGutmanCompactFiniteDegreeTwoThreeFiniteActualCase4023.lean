/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4023 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap4023 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,10,8,9,2,1,0,11,12,13,14,15] (sourceLabel 5 1 7 v)
def fusedMap4023 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 1 7 v)
theorem sourceMap4023_checked : acceptsGraphIso
    (source (graph core4023) (root 5) 1 7) DegreeTwoThreeSpectrum4210.graph sourceMap4023=true := by decide +kernel
theorem fusedMap4023_checked : acceptsGraphIso
    (fused (graph core4023) (root 5) 1 7) DegreeTwoThreeSpectrum3902.graph fusedMap4023=true := by decide +kernel
theorem certified4023 : Certified (graph core4023) (root 5) 1 7 :=
  of_native_maps core4023 DegreeTwoThreeSpectrum4210.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap4023 fusedMap4023 sourceMap4023_checked fusedMap4023_checked
    DegreeTwoThreeFiniteComparisons.comparison4023
#print axioms sourceMap4023_checked
#print axioms fusedMap4023_checked
#print axioms certified4023
def sourceMap4023swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 2) → Fin 16 :=
  fun v => ![3,4,5,6,7,10,2,1,0,11,12,13,14,15,8,9] (sourceLabel 5 7 1 v)
def fusedMap4023swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 7 1 v)
theorem sourceMap4023swap_checked : acceptsGraphIso
    (source (graph core4023) (root 5) 7 1) DegreeTwoThreeSpectrum4210.graph sourceMap4023swap=true := by decide +kernel
theorem fusedMap4023swap_checked : acceptsGraphIso
    (fused (graph core4023) (root 5) 7 1) DegreeTwoThreeSpectrum3902.graph fusedMap4023swap=true := by decide +kernel
theorem certified4023swap : Certified (graph core4023) (root 5) 7 1 :=
  of_native_maps core4023 DegreeTwoThreeSpectrum4210.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap4023swap fusedMap4023swap sourceMap4023swap_checked fusedMap4023swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4023
#print axioms sourceMap4023swap_checked
#print axioms fusedMap4023swap_checked
#print axioms certified4023swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
