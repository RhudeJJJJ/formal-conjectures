/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3019 : Family 10 := level10.get ⟨1616,by decide⟩
def sourceMap3019 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3019 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3019_checked : acceptsGraphIso
    (source (graph core3019) (root 10) 0 4) DegreeTwoThreeSpectrum7174.graph sourceMap3019=true := by decide +kernel
theorem fusedMap3019_checked : acceptsGraphIso
    (fused (graph core3019) (root 10) 0 4) DegreeTwoThreeSpectrum6172.graph fusedMap3019=true := by decide +kernel
theorem certified3019 : Certified (graph core3019) (root 10) 0 4 :=
  of_native_maps core3019 DegreeTwoThreeSpectrum7174.graph DegreeTwoThreeSpectrum6172.graph
    sourceMap3019 fusedMap3019 sourceMap3019_checked fusedMap3019_checked
    DegreeTwoThreeFiniteComparisons.comparison3019
#print axioms sourceMap3019_checked
#print axioms fusedMap3019_checked
#print axioms certified3019
def sourceMap3019swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3019swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3019swap_checked : acceptsGraphIso
    (source (graph core3019) (root 10) 4 0) DegreeTwoThreeSpectrum7174.graph sourceMap3019swap=true := by decide +kernel
theorem fusedMap3019swap_checked : acceptsGraphIso
    (fused (graph core3019) (root 10) 4 0) DegreeTwoThreeSpectrum6172.graph fusedMap3019swap=true := by decide +kernel
theorem certified3019swap : Certified (graph core3019) (root 10) 4 0 :=
  of_native_maps core3019 DegreeTwoThreeSpectrum7174.graph DegreeTwoThreeSpectrum6172.graph
    sourceMap3019swap fusedMap3019swap sourceMap3019swap_checked fusedMap3019swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3019
#print axioms sourceMap3019swap_checked
#print axioms fusedMap3019swap_checked
#print axioms certified3019swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
