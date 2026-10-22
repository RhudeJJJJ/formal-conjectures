/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3518 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap3518 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3518 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3518_checked : acceptsGraphIso
    (source (graph core3518) (root 7) 0 6) DegreeTwoThreeSpectrum4094.graph sourceMap3518=true := by decide +kernel
theorem fusedMap3518_checked : acceptsGraphIso
    (fused (graph core3518) (root 7) 0 6) DegreeTwoThreeSpectrum4096.graph fusedMap3518=true := by decide +kernel
theorem certified3518 : Certified (graph core3518) (root 7) 0 6 :=
  of_native_maps core3518 DegreeTwoThreeSpectrum4094.graph DegreeTwoThreeSpectrum4096.graph
    sourceMap3518 fusedMap3518 sourceMap3518_checked fusedMap3518_checked
    DegreeTwoThreeFiniteComparisons.comparison3518
#print axioms sourceMap3518_checked
#print axioms fusedMap3518_checked
#print axioms certified3518
def sourceMap3518swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3518swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3518swap_checked : acceptsGraphIso
    (source (graph core3518) (root 7) 6 0) DegreeTwoThreeSpectrum4094.graph sourceMap3518swap=true := by decide +kernel
theorem fusedMap3518swap_checked : acceptsGraphIso
    (fused (graph core3518) (root 7) 6 0) DegreeTwoThreeSpectrum4096.graph fusedMap3518swap=true := by decide +kernel
theorem certified3518swap : Certified (graph core3518) (root 7) 6 0 :=
  of_native_maps core3518 DegreeTwoThreeSpectrum4094.graph DegreeTwoThreeSpectrum4096.graph
    sourceMap3518swap fusedMap3518swap sourceMap3518swap_checked fusedMap3518swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3518
#print axioms sourceMap3518swap_checked
#print axioms fusedMap3518swap_checked
#print axioms certified3518swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
