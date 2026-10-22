/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4018 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap4018 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (sourceLabel 4 1 7 v)
def fusedMap4018 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 1 7 v)
theorem sourceMap4018_checked : acceptsGraphIso
    (source (graph core4018) (root 4) 1 7) DegreeTwoThreeSpectrum2648.graph sourceMap4018=true := by decide +kernel
theorem fusedMap4018_checked : acceptsGraphIso
    (fused (graph core4018) (root 4) 1 7) DegreeTwoThreeSpectrum2354.graph fusedMap4018=true := by decide +kernel
theorem certified4018 : Certified (graph core4018) (root 4) 1 7 :=
  of_native_maps core4018 DegreeTwoThreeSpectrum2648.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap4018 fusedMap4018 sourceMap4018_checked fusedMap4018_checked
    DegreeTwoThreeFiniteComparisons.comparison4018
#print axioms sourceMap4018_checked
#print axioms fusedMap4018_checked
#print axioms certified4018
def sourceMap4018swap : (Vertices 4 ⊕ Fin 8 ⊕ Fin 2) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,10,11,12,13,14,8,9] (sourceLabel 4 7 1 v)
def fusedMap4018swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 7 1 v)
theorem sourceMap4018swap_checked : acceptsGraphIso
    (source (graph core4018) (root 4) 7 1) DegreeTwoThreeSpectrum2648.graph sourceMap4018swap=true := by decide +kernel
theorem fusedMap4018swap_checked : acceptsGraphIso
    (fused (graph core4018) (root 4) 7 1) DegreeTwoThreeSpectrum2354.graph fusedMap4018swap=true := by decide +kernel
theorem certified4018swap : Certified (graph core4018) (root 4) 7 1 :=
  of_native_maps core4018 DegreeTwoThreeSpectrum2648.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap4018swap fusedMap4018swap sourceMap4018swap_checked fusedMap4018swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4018
#print axioms sourceMap4018swap_checked
#print axioms fusedMap4018swap_checked
#print axioms certified4018swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
