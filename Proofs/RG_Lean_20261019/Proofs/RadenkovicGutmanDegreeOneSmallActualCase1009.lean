/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1009 : Family 8 := level8.get ⟨103,by decide⟩
def sourceMap1009 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1009 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1009_checked : acceptsGraphIso
    (source (graph core1009) (root 8) 0 2) DegreeOneSmallSpectrum1043.graph sourceMap1009=true := by decide +kernel
theorem fusedMap1009_checked : acceptsGraphIso
    (fused (graph core1009) (root 8) 0 2) DegreeOneSmallSpectrum1044.graph fusedMap1009=true := by decide +kernel
theorem certified1009 : Certified (graph core1009) (root 8) 0 2 :=
  of_native_maps core1009 DegreeOneSmallSpectrum1043.graph DegreeOneSmallSpectrum1044.graph
    sourceMap1009 fusedMap1009 sourceMap1009_checked fusedMap1009_checked
    DegreeOneSmallComparisons.comparison1009
#print axioms sourceMap1009_checked
#print axioms fusedMap1009_checked
#print axioms certified1009
def sourceMap1009swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1009swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1009swap_checked : acceptsGraphIso
    (source (graph core1009) (root 8) 2 0) DegreeOneSmallSpectrum1043.graph sourceMap1009swap=true := by decide +kernel
theorem fusedMap1009swap_checked : acceptsGraphIso
    (fused (graph core1009) (root 8) 2 0) DegreeOneSmallSpectrum1044.graph fusedMap1009swap=true := by decide +kernel
theorem certified1009swap : Certified (graph core1009) (root 8) 2 0 :=
  of_native_maps core1009 DegreeOneSmallSpectrum1043.graph DegreeOneSmallSpectrum1044.graph
    sourceMap1009swap fusedMap1009swap sourceMap1009swap_checked fusedMap1009swap_checked
    DegreeOneSmallComparisons.comparison1009
#print axioms sourceMap1009swap_checked
#print axioms fusedMap1009swap_checked
#print axioms certified1009swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
