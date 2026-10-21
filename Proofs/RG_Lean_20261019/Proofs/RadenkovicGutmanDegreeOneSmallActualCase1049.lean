/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1049 : Family 8 := level8.get ⟨121,by decide⟩
def sourceMap1049 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1049 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1049_checked : acceptsGraphIso
    (source (graph core1049) (root 8) 0 2) DegreeOneSmallSpectrum1194.graph sourceMap1049=true := by decide +kernel
theorem fusedMap1049_checked : acceptsGraphIso
    (fused (graph core1049) (root 8) 0 2) DegreeOneSmallSpectrum1195.graph fusedMap1049=true := by decide +kernel
theorem certified1049 : Certified (graph core1049) (root 8) 0 2 :=
  of_native_maps core1049 DegreeOneSmallSpectrum1194.graph DegreeOneSmallSpectrum1195.graph
    sourceMap1049 fusedMap1049 sourceMap1049_checked fusedMap1049_checked
    DegreeOneSmallComparisons.comparison1049
#print axioms sourceMap1049_checked
#print axioms fusedMap1049_checked
#print axioms certified1049
def sourceMap1049swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1049swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1049swap_checked : acceptsGraphIso
    (source (graph core1049) (root 8) 2 0) DegreeOneSmallSpectrum1194.graph sourceMap1049swap=true := by decide +kernel
theorem fusedMap1049swap_checked : acceptsGraphIso
    (fused (graph core1049) (root 8) 2 0) DegreeOneSmallSpectrum1195.graph fusedMap1049swap=true := by decide +kernel
theorem certified1049swap : Certified (graph core1049) (root 8) 2 0 :=
  of_native_maps core1049 DegreeOneSmallSpectrum1194.graph DegreeOneSmallSpectrum1195.graph
    sourceMap1049swap fusedMap1049swap sourceMap1049swap_checked fusedMap1049swap_checked
    DegreeOneSmallComparisons.comparison1049
#print axioms sourceMap1049swap_checked
#print axioms fusedMap1049swap_checked
#print axioms certified1049swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
