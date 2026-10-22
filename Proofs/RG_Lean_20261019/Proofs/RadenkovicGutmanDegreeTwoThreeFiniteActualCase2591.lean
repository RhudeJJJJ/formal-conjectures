/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2591 : Family 10 := level10.get ⟨501,by decide⟩
def sourceMap2591 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2591 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2591_checked : acceptsGraphIso
    (source (graph core2591) (root 10) 0 4) DegreeTwoThreeSpectrum5992.graph sourceMap2591=true := by decide +kernel
theorem fusedMap2591_checked : acceptsGraphIso
    (fused (graph core2591) (root 10) 0 4) DegreeTwoThreeSpectrum5138.graph fusedMap2591=true := by decide +kernel
theorem certified2591 : Certified (graph core2591) (root 10) 0 4 :=
  of_native_maps core2591 DegreeTwoThreeSpectrum5992.graph DegreeTwoThreeSpectrum5138.graph
    sourceMap2591 fusedMap2591 sourceMap2591_checked fusedMap2591_checked
    DegreeTwoThreeFiniteComparisons.comparison2591
#print axioms sourceMap2591_checked
#print axioms fusedMap2591_checked
#print axioms certified2591
def sourceMap2591swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2591swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2591swap_checked : acceptsGraphIso
    (source (graph core2591) (root 10) 4 0) DegreeTwoThreeSpectrum5992.graph sourceMap2591swap=true := by decide +kernel
theorem fusedMap2591swap_checked : acceptsGraphIso
    (fused (graph core2591) (root 10) 4 0) DegreeTwoThreeSpectrum5138.graph fusedMap2591swap=true := by decide +kernel
theorem certified2591swap : Certified (graph core2591) (root 10) 4 0 :=
  of_native_maps core2591 DegreeTwoThreeSpectrum5992.graph DegreeTwoThreeSpectrum5138.graph
    sourceMap2591swap fusedMap2591swap sourceMap2591swap_checked fusedMap2591swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2591
#print axioms sourceMap2591swap_checked
#print axioms fusedMap2591swap_checked
#print axioms certified2591swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
