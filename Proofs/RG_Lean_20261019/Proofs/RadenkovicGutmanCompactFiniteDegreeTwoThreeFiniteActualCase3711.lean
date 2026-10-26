/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3711 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap3711 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3711 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3711_checked : acceptsGraphIso
    (source (graph core3711) (root 6) 0 8) DegreeTwoThreeSpectrum4989.graph sourceMap3711=true := by decide +kernel
theorem fusedMap3711_checked : acceptsGraphIso
    (fused (graph core3711) (root 6) 0 8) DegreeTwoThreeSpectrum4993.graph fusedMap3711=true := by decide +kernel
theorem certified3711 : Certified (graph core3711) (root 6) 0 8 :=
  of_native_maps core3711 DegreeTwoThreeSpectrum4989.graph DegreeTwoThreeSpectrum4993.graph
    sourceMap3711 fusedMap3711 sourceMap3711_checked fusedMap3711_checked
    DegreeTwoThreeFiniteComparisons.comparison3711
#print axioms sourceMap3711_checked
#print axioms fusedMap3711_checked
#print axioms certified3711
def sourceMap3711swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,16,9] (sourceLabel 6 8 0 v)
def fusedMap3711swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3711swap_checked : acceptsGraphIso
    (source (graph core3711) (root 6) 8 0) DegreeTwoThreeSpectrum4989.graph sourceMap3711swap=true := by decide +kernel
theorem fusedMap3711swap_checked : acceptsGraphIso
    (fused (graph core3711) (root 6) 8 0) DegreeTwoThreeSpectrum4993.graph fusedMap3711swap=true := by decide +kernel
theorem certified3711swap : Certified (graph core3711) (root 6) 8 0 :=
  of_native_maps core3711 DegreeTwoThreeSpectrum4989.graph DegreeTwoThreeSpectrum4993.graph
    sourceMap3711swap fusedMap3711swap sourceMap3711swap_checked fusedMap3711swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3711
#print axioms sourceMap3711swap_checked
#print axioms fusedMap3711swap_checked
#print axioms certified3711swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
