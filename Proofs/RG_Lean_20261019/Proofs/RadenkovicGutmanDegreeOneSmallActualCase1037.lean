/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1037 : Family 8 := level8.get ⟨115,by decide⟩
def sourceMap1037 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1037 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1037_checked : acceptsGraphIso
    (source (graph core1037) (root 8) 0 2) DegreeOneSmallSpectrum1141.graph sourceMap1037=true := by decide +kernel
theorem fusedMap1037_checked : acceptsGraphIso
    (fused (graph core1037) (root 8) 0 2) DegreeOneSmallSpectrum1142.graph fusedMap1037=true := by decide +kernel
theorem certified1037 : Certified (graph core1037) (root 8) 0 2 :=
  of_native_maps core1037 DegreeOneSmallSpectrum1141.graph DegreeOneSmallSpectrum1142.graph
    sourceMap1037 fusedMap1037 sourceMap1037_checked fusedMap1037_checked
    DegreeOneSmallComparisons.comparison1037
#print axioms sourceMap1037_checked
#print axioms fusedMap1037_checked
#print axioms certified1037
def sourceMap1037swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1037swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1037swap_checked : acceptsGraphIso
    (source (graph core1037) (root 8) 2 0) DegreeOneSmallSpectrum1141.graph sourceMap1037swap=true := by decide +kernel
theorem fusedMap1037swap_checked : acceptsGraphIso
    (fused (graph core1037) (root 8) 2 0) DegreeOneSmallSpectrum1142.graph fusedMap1037swap=true := by decide +kernel
theorem certified1037swap : Certified (graph core1037) (root 8) 2 0 :=
  of_native_maps core1037 DegreeOneSmallSpectrum1141.graph DegreeOneSmallSpectrum1142.graph
    sourceMap1037swap fusedMap1037swap sourceMap1037swap_checked fusedMap1037swap_checked
    DegreeOneSmallComparisons.comparison1037
#print axioms sourceMap1037swap_checked
#print axioms fusedMap1037swap_checked
#print axioms certified1037swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
