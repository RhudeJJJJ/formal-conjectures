/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3979 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap3979 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3979 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3979_checked : acceptsGraphIso
    (source (graph core3979) (root 7) 1 5) DegreeTwoThreeSpectrum4447.graph sourceMap3979=true := by decide +kernel
theorem fusedMap3979_checked : acceptsGraphIso
    (fused (graph core3979) (root 7) 1 5) DegreeTwoThreeSpectrum4001.graph fusedMap3979=true := by decide +kernel
theorem certified3979 : Certified (graph core3979) (root 7) 1 5 :=
  of_native_maps core3979 DegreeTwoThreeSpectrum4447.graph DegreeTwoThreeSpectrum4001.graph
    sourceMap3979 fusedMap3979 sourceMap3979_checked fusedMap3979_checked
    DegreeTwoThreeFiniteComparisons.comparison3979
#print axioms sourceMap3979_checked
#print axioms fusedMap3979_checked
#print axioms certified3979
def sourceMap3979swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3979swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3979swap_checked : acceptsGraphIso
    (source (graph core3979) (root 7) 5 1) DegreeTwoThreeSpectrum4447.graph sourceMap3979swap=true := by decide +kernel
theorem fusedMap3979swap_checked : acceptsGraphIso
    (fused (graph core3979) (root 7) 5 1) DegreeTwoThreeSpectrum4001.graph fusedMap3979swap=true := by decide +kernel
theorem certified3979swap : Certified (graph core3979) (root 7) 5 1 :=
  of_native_maps core3979 DegreeTwoThreeSpectrum4447.graph DegreeTwoThreeSpectrum4001.graph
    sourceMap3979swap fusedMap3979swap sourceMap3979swap_checked fusedMap3979swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3979
#print axioms sourceMap3979swap_checked
#print axioms fusedMap3979swap_checked
#print axioms certified3979swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
