/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3737 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3737 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 11) → Fin 15 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14] (sourceLabel 2 0 10 v)
def fusedMap3737 : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 0 10 v)
theorem sourceMap3737_checked : acceptsGraphIso
    (source (graph core3737) (root 2) 0 10) DegreeTwoThreeSpectrum2320.graph sourceMap3737=true := by decide +kernel
theorem fusedMap3737_checked : acceptsGraphIso
    (fused (graph core3737) (root 2) 0 10) DegreeTwoThreeSpectrum2309.graph fusedMap3737=true := by decide +kernel
theorem certified3737 : Certified (graph core3737) (root 2) 0 10 :=
  of_native_maps core3737 DegreeTwoThreeSpectrum2320.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap3737 fusedMap3737 sourceMap3737_checked fusedMap3737_checked
    DegreeTwoThreeFiniteComparisons.comparison3737
#print axioms sourceMap3737_checked
#print axioms fusedMap3737_checked
#print axioms certified3737
def sourceMap3737swap : (Vertices 2 ⊕ Fin 11 ⊕ Fin 1) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,9,10,11,12,13,14,8] (sourceLabel 2 10 0 v)
def fusedMap3737swap : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 10 0 v)
theorem sourceMap3737swap_checked : acceptsGraphIso
    (source (graph core3737) (root 2) 10 0) DegreeTwoThreeSpectrum2320.graph sourceMap3737swap=true := by decide +kernel
theorem fusedMap3737swap_checked : acceptsGraphIso
    (fused (graph core3737) (root 2) 10 0) DegreeTwoThreeSpectrum2309.graph fusedMap3737swap=true := by decide +kernel
theorem certified3737swap : Certified (graph core3737) (root 2) 10 0 :=
  of_native_maps core3737 DegreeTwoThreeSpectrum2320.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap3737swap fusedMap3737swap sourceMap3737swap_checked fusedMap3737swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3737
#print axioms sourceMap3737swap_checked
#print axioms fusedMap3737swap_checked
#print axioms certified3737swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
