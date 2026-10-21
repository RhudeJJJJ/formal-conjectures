/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1877 : Family 10 := level10.get ⟨140,by decide⟩
def sourceMap1877 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1877 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1877_checked : acceptsGraphIso
    (source (graph core1877) (root 10) 0 0) DegreeOneSmallSpectrum1111.graph sourceMap1877=true := by decide +kernel
theorem fusedMap1877_checked : acceptsGraphIso
    (fused (graph core1877) (root 10) 0 0) DegreeOneSmallSpectrum949.graph fusedMap1877=true := by decide +kernel
theorem certified1877 : Certified (graph core1877) (root 10) 0 0 :=
  of_native_maps core1877 DegreeOneSmallSpectrum1111.graph DegreeOneSmallSpectrum949.graph
    sourceMap1877 fusedMap1877 sourceMap1877_checked fusedMap1877_checked
    DegreeOneSmallComparisons.comparison1877
#print axioms sourceMap1877_checked
#print axioms fusedMap1877_checked
#print axioms certified1877
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
