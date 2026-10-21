/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1157 : Family 8 := level8.get ⟨197,by decide⟩
def sourceMap1157 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1157 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1157_checked : acceptsGraphIso
    (source (graph core1157) (root 8) 0 2) DegreeOneSmallSpectrum1629.graph sourceMap1157=true := by decide +kernel
theorem fusedMap1157_checked : acceptsGraphIso
    (fused (graph core1157) (root 8) 0 2) DegreeOneSmallSpectrum1010.graph fusedMap1157=true := by decide +kernel
theorem certified1157 : Certified (graph core1157) (root 8) 0 2 :=
  of_native_maps core1157 DegreeOneSmallSpectrum1629.graph DegreeOneSmallSpectrum1010.graph
    sourceMap1157 fusedMap1157 sourceMap1157_checked fusedMap1157_checked
    DegreeOneSmallComparisons.comparison1157
#print axioms sourceMap1157_checked
#print axioms fusedMap1157_checked
#print axioms certified1157
def sourceMap1157swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1157swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1157swap_checked : acceptsGraphIso
    (source (graph core1157) (root 8) 2 0) DegreeOneSmallSpectrum1629.graph sourceMap1157swap=true := by decide +kernel
theorem fusedMap1157swap_checked : acceptsGraphIso
    (fused (graph core1157) (root 8) 2 0) DegreeOneSmallSpectrum1010.graph fusedMap1157swap=true := by decide +kernel
theorem certified1157swap : Certified (graph core1157) (root 8) 2 0 :=
  of_native_maps core1157 DegreeOneSmallSpectrum1629.graph DegreeOneSmallSpectrum1010.graph
    sourceMap1157swap fusedMap1157swap sourceMap1157swap_checked fusedMap1157swap_checked
    DegreeOneSmallComparisons.comparison1157
#print axioms sourceMap1157swap_checked
#print axioms fusedMap1157swap_checked
#print axioms certified1157swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
