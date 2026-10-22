/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2573 : Family 10 := level10.get ⟨453,by decide⟩
def sourceMap2573 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2573 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2573_checked : acceptsGraphIso
    (source (graph core2573) (root 10) 0 4) DegreeTwoThreeSpectrum5881.graph sourceMap2573=true := by decide +kernel
theorem fusedMap2573_checked : acceptsGraphIso
    (fused (graph core2573) (root 10) 0 4) DegreeTwoThreeSpectrum5883.graph fusedMap2573=true := by decide +kernel
theorem certified2573 : Certified (graph core2573) (root 10) 0 4 :=
  of_native_maps core2573 DegreeTwoThreeSpectrum5881.graph DegreeTwoThreeSpectrum5883.graph
    sourceMap2573 fusedMap2573 sourceMap2573_checked fusedMap2573_checked
    DegreeTwoThreeFiniteComparisons.comparison2573
#print axioms sourceMap2573_checked
#print axioms fusedMap2573_checked
#print axioms certified2573
def sourceMap2573swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2573swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2573swap_checked : acceptsGraphIso
    (source (graph core2573) (root 10) 4 0) DegreeTwoThreeSpectrum5881.graph sourceMap2573swap=true := by decide +kernel
theorem fusedMap2573swap_checked : acceptsGraphIso
    (fused (graph core2573) (root 10) 4 0) DegreeTwoThreeSpectrum5883.graph fusedMap2573swap=true := by decide +kernel
theorem certified2573swap : Certified (graph core2573) (root 10) 4 0 :=
  of_native_maps core2573 DegreeTwoThreeSpectrum5881.graph DegreeTwoThreeSpectrum5883.graph
    sourceMap2573swap fusedMap2573swap sourceMap2573swap_checked fusedMap2573swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2573
#print axioms sourceMap2573swap_checked
#print axioms fusedMap2573swap_checked
#print axioms certified2573swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
