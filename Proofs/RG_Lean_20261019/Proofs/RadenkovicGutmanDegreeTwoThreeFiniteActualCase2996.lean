/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2996 : Family 10 := level10.get ⟨1558,by decide⟩
def sourceMap2996 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2996 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2996_checked : acceptsGraphIso
    (source (graph core2996) (root 10) 0 4) DegreeTwoThreeSpectrum7096.graph sourceMap2996=true := by decide +kernel
theorem fusedMap2996_checked : acceptsGraphIso
    (fused (graph core2996) (root 10) 0 4) DegreeTwoThreeSpectrum6021.graph fusedMap2996=true := by decide +kernel
theorem certified2996 : Certified (graph core2996) (root 10) 0 4 :=
  of_native_maps core2996 DegreeTwoThreeSpectrum7096.graph DegreeTwoThreeSpectrum6021.graph
    sourceMap2996 fusedMap2996 sourceMap2996_checked fusedMap2996_checked
    DegreeTwoThreeFiniteComparisons.comparison2996
#print axioms sourceMap2996_checked
#print axioms fusedMap2996_checked
#print axioms certified2996
def sourceMap2996swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2996swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2996swap_checked : acceptsGraphIso
    (source (graph core2996) (root 10) 4 0) DegreeTwoThreeSpectrum7096.graph sourceMap2996swap=true := by decide +kernel
theorem fusedMap2996swap_checked : acceptsGraphIso
    (fused (graph core2996) (root 10) 4 0) DegreeTwoThreeSpectrum6021.graph fusedMap2996swap=true := by decide +kernel
theorem certified2996swap : Certified (graph core2996) (root 10) 4 0 :=
  of_native_maps core2996 DegreeTwoThreeSpectrum7096.graph DegreeTwoThreeSpectrum6021.graph
    sourceMap2996swap fusedMap2996swap sourceMap2996swap_checked fusedMap2996swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2996
#print axioms sourceMap2996swap_checked
#print axioms fusedMap2996swap_checked
#print axioms certified2996swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
