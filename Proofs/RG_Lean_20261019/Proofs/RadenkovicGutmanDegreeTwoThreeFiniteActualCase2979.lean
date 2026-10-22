/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2979 : Family 10 := level10.get ⟨1504,by decide⟩
def sourceMap2979 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2979 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2979_checked : acceptsGraphIso
    (source (graph core2979) (root 10) 0 4) DegreeTwoThreeSpectrum7010.graph sourceMap2979=true := by decide +kernel
theorem fusedMap2979_checked : acceptsGraphIso
    (fused (graph core2979) (root 10) 0 4) DegreeTwoThreeSpectrum7011.graph fusedMap2979=true := by decide +kernel
theorem certified2979 : Certified (graph core2979) (root 10) 0 4 :=
  of_native_maps core2979 DegreeTwoThreeSpectrum7010.graph DegreeTwoThreeSpectrum7011.graph
    sourceMap2979 fusedMap2979 sourceMap2979_checked fusedMap2979_checked
    DegreeTwoThreeFiniteComparisons.comparison2979
#print axioms sourceMap2979_checked
#print axioms fusedMap2979_checked
#print axioms certified2979
def sourceMap2979swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2979swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2979swap_checked : acceptsGraphIso
    (source (graph core2979) (root 10) 4 0) DegreeTwoThreeSpectrum7010.graph sourceMap2979swap=true := by decide +kernel
theorem fusedMap2979swap_checked : acceptsGraphIso
    (fused (graph core2979) (root 10) 4 0) DegreeTwoThreeSpectrum7011.graph fusedMap2979swap=true := by decide +kernel
theorem certified2979swap : Certified (graph core2979) (root 10) 4 0 :=
  of_native_maps core2979 DegreeTwoThreeSpectrum7010.graph DegreeTwoThreeSpectrum7011.graph
    sourceMap2979swap fusedMap2979swap sourceMap2979swap_checked fusedMap2979swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2979
#print axioms sourceMap2979swap_checked
#print axioms fusedMap2979swap_checked
#print axioms certified2979swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
