/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1844 : Family 10 := level10.get ⟨96,by decide⟩
def sourceMap1844 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1844 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1844_checked : acceptsGraphIso
    (source (graph core1844) (root 10) 0 0) DegreeOneSmallSpectrum1234.graph sourceMap1844=true := by decide +kernel
theorem fusedMap1844_checked : acceptsGraphIso
    (fused (graph core1844) (root 10) 0 0) DegreeOneSmallSpectrum921.graph fusedMap1844=true := by decide +kernel
theorem certified1844 : Certified (graph core1844) (root 10) 0 0 :=
  of_native_maps core1844 DegreeOneSmallSpectrum1234.graph DegreeOneSmallSpectrum921.graph
    sourceMap1844 fusedMap1844 sourceMap1844_checked fusedMap1844_checked
    DegreeOneSmallComparisons.comparison1844
#print axioms sourceMap1844_checked
#print axioms fusedMap1844_checked
#print axioms certified1844
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
