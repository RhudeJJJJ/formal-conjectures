/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1370 : Family 9 := level9.get ⟨117,by decide⟩
def sourceMap1370 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1370 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1370_checked : acceptsGraphIso
    (source (graph core1370) (root 9) 0 1) DegreeOneSmallSpectrum1455.graph sourceMap1370=true := by decide +kernel
theorem fusedMap1370_checked : acceptsGraphIso
    (fused (graph core1370) (root 9) 0 1) DegreeOneSmallSpectrum972.graph fusedMap1370=true := by decide +kernel
theorem certified1370 : Certified (graph core1370) (root 9) 0 1 :=
  of_native_maps core1370 DegreeOneSmallSpectrum1455.graph DegreeOneSmallSpectrum972.graph
    sourceMap1370 fusedMap1370 sourceMap1370_checked fusedMap1370_checked
    DegreeOneSmallComparisons.comparison1370
#print axioms sourceMap1370_checked
#print axioms fusedMap1370_checked
#print axioms certified1370
def sourceMap1370swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1370swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1370swap_checked : acceptsGraphIso
    (source (graph core1370) (root 9) 1 0) DegreeOneSmallSpectrum1455.graph sourceMap1370swap=true := by decide +kernel
theorem fusedMap1370swap_checked : acceptsGraphIso
    (fused (graph core1370) (root 9) 1 0) DegreeOneSmallSpectrum972.graph fusedMap1370swap=true := by decide +kernel
theorem certified1370swap : Certified (graph core1370) (root 9) 1 0 :=
  of_native_maps core1370 DegreeOneSmallSpectrum1455.graph DegreeOneSmallSpectrum972.graph
    sourceMap1370swap fusedMap1370swap sourceMap1370swap_checked fusedMap1370swap_checked
    DegreeOneSmallComparisons.comparison1370
#print axioms sourceMap1370swap_checked
#print axioms fusedMap1370swap_checked
#print axioms certified1370swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
