/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2632 : Family 10 := level10.get ⟨631,by decide⟩
def sourceMap2632 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2632 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2632_checked : acceptsGraphIso
    (source (graph core2632) (root 10) 0 4) DegreeTwoThreeSpectrum6383.graph sourceMap2632=true := by decide +kernel
theorem fusedMap2632_checked : acceptsGraphIso
    (fused (graph core2632) (root 10) 0 4) DegreeTwoThreeSpectrum5323.graph fusedMap2632=true := by decide +kernel
theorem certified2632 : Certified (graph core2632) (root 10) 0 4 :=
  of_native_maps core2632 DegreeTwoThreeSpectrum6383.graph DegreeTwoThreeSpectrum5323.graph
    sourceMap2632 fusedMap2632 sourceMap2632_checked fusedMap2632_checked
    DegreeTwoThreeFiniteComparisons.comparison2632
#print axioms sourceMap2632_checked
#print axioms fusedMap2632_checked
#print axioms certified2632
def sourceMap2632swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2632swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2632swap_checked : acceptsGraphIso
    (source (graph core2632) (root 10) 4 0) DegreeTwoThreeSpectrum6383.graph sourceMap2632swap=true := by decide +kernel
theorem fusedMap2632swap_checked : acceptsGraphIso
    (fused (graph core2632) (root 10) 4 0) DegreeTwoThreeSpectrum5323.graph fusedMap2632swap=true := by decide +kernel
theorem certified2632swap : Certified (graph core2632) (root 10) 4 0 :=
  of_native_maps core2632 DegreeTwoThreeSpectrum6383.graph DegreeTwoThreeSpectrum5323.graph
    sourceMap2632swap fusedMap2632swap sourceMap2632swap_checked fusedMap2632swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2632
#print axioms sourceMap2632swap_checked
#print axioms fusedMap2632swap_checked
#print axioms certified2632swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
