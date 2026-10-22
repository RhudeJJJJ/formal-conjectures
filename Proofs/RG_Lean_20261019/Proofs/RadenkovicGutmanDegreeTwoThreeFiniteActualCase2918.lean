/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2918 : Family 10 := level10.get ⟨1363,by decide⟩
def sourceMap2918 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2918 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2918_checked : acceptsGraphIso
    (source (graph core2918) (root 10) 0 4) DegreeTwoThreeSpectrum6699.graph sourceMap2918=true := by decide +kernel
theorem fusedMap2918_checked : acceptsGraphIso
    (fused (graph core2918) (root 10) 0 4) DegreeTwoThreeSpectrum6700.graph fusedMap2918=true := by decide +kernel
theorem certified2918 : Certified (graph core2918) (root 10) 0 4 :=
  of_native_maps core2918 DegreeTwoThreeSpectrum6699.graph DegreeTwoThreeSpectrum6700.graph
    sourceMap2918 fusedMap2918 sourceMap2918_checked fusedMap2918_checked
    DegreeTwoThreeFiniteComparisons.comparison2918
#print axioms sourceMap2918_checked
#print axioms fusedMap2918_checked
#print axioms certified2918
def sourceMap2918swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2918swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2918swap_checked : acceptsGraphIso
    (source (graph core2918) (root 10) 4 0) DegreeTwoThreeSpectrum6699.graph sourceMap2918swap=true := by decide +kernel
theorem fusedMap2918swap_checked : acceptsGraphIso
    (fused (graph core2918) (root 10) 4 0) DegreeTwoThreeSpectrum6700.graph fusedMap2918swap=true := by decide +kernel
theorem certified2918swap : Certified (graph core2918) (root 10) 4 0 :=
  of_native_maps core2918 DegreeTwoThreeSpectrum6699.graph DegreeTwoThreeSpectrum6700.graph
    sourceMap2918swap fusedMap2918swap sourceMap2918swap_checked fusedMap2918swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2918
#print axioms sourceMap2918swap_checked
#print axioms fusedMap2918swap_checked
#print axioms certified2918swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
