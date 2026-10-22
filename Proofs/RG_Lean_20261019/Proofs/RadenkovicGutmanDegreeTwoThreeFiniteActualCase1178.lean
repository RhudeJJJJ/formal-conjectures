/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1178 : Family 8 := level8.get ⟨234,by decide⟩
def sourceMap1178 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1178 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1178_checked : acceptsGraphIso
    (source (graph core1178) (root 8) 0 2) DegreeOneSmallSpectrum1913.graph sourceMap1178=true := by decide +kernel
theorem fusedMap1178_checked : acceptsGraphIso
    (fused (graph core1178) (root 8) 0 2) DegreeOneSmallSpectrum1302.graph fusedMap1178=true := by decide +kernel
theorem certified1178 : Certified (graph core1178) (root 8) 0 2 :=
  of_native_maps core1178 DegreeOneSmallSpectrum1913.graph DegreeOneSmallSpectrum1302.graph
    sourceMap1178 fusedMap1178 sourceMap1178_checked fusedMap1178_checked
    DegreeTwoThreeFiniteComparisons.comparison1178
#print axioms sourceMap1178_checked
#print axioms fusedMap1178_checked
#print axioms certified1178
def sourceMap1178swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1178swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1178swap_checked : acceptsGraphIso
    (source (graph core1178) (root 8) 2 0) DegreeOneSmallSpectrum1913.graph sourceMap1178swap=true := by decide +kernel
theorem fusedMap1178swap_checked : acceptsGraphIso
    (fused (graph core1178) (root 8) 2 0) DegreeOneSmallSpectrum1302.graph fusedMap1178swap=true := by decide +kernel
theorem certified1178swap : Certified (graph core1178) (root 8) 2 0 :=
  of_native_maps core1178 DegreeOneSmallSpectrum1913.graph DegreeOneSmallSpectrum1302.graph
    sourceMap1178swap fusedMap1178swap sourceMap1178swap_checked fusedMap1178swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1178
#print axioms sourceMap1178swap_checked
#print axioms fusedMap1178swap_checked
#print axioms certified1178swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
