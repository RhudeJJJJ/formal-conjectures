/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2989 : Family 10 := level10.get ⟨1544,by decide⟩
def sourceMap2989 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2989 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2989_checked : acceptsGraphIso
    (source (graph core2989) (root 10) 0 4) DegreeTwoThreeSpectrum7084.graph sourceMap2989=true := by decide +kernel
theorem fusedMap2989_checked : acceptsGraphIso
    (fused (graph core2989) (root 10) 0 4) DegreeTwoThreeSpectrum5995.graph fusedMap2989=true := by decide +kernel
theorem certified2989 : Certified (graph core2989) (root 10) 0 4 :=
  of_native_maps core2989 DegreeTwoThreeSpectrum7084.graph DegreeTwoThreeSpectrum5995.graph
    sourceMap2989 fusedMap2989 sourceMap2989_checked fusedMap2989_checked
    DegreeTwoThreeFiniteComparisons.comparison2989
#print axioms sourceMap2989_checked
#print axioms fusedMap2989_checked
#print axioms certified2989
def sourceMap2989swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2989swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2989swap_checked : acceptsGraphIso
    (source (graph core2989) (root 10) 4 0) DegreeTwoThreeSpectrum7084.graph sourceMap2989swap=true := by decide +kernel
theorem fusedMap2989swap_checked : acceptsGraphIso
    (fused (graph core2989) (root 10) 4 0) DegreeTwoThreeSpectrum5995.graph fusedMap2989swap=true := by decide +kernel
theorem certified2989swap : Certified (graph core2989) (root 10) 4 0 :=
  of_native_maps core2989 DegreeTwoThreeSpectrum7084.graph DegreeTwoThreeSpectrum5995.graph
    sourceMap2989swap fusedMap2989swap sourceMap2989swap_checked fusedMap2989swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2989
#print axioms sourceMap2989swap_checked
#print axioms fusedMap2989swap_checked
#print axioms certified2989swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
