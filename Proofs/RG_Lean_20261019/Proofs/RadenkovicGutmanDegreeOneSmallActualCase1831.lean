/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1831 : Family 10 := level10.get ⟨78,by decide⟩
def sourceMap1831 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1831 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1831_checked : acceptsGraphIso
    (source (graph core1831) (root 10) 0 0) DegreeOneSmallSpectrum1203.graph sourceMap1831=true := by decide +kernel
theorem fusedMap1831_checked : acceptsGraphIso
    (fused (graph core1831) (root 10) 0 0) DegreeOneSmallSpectrum905.graph fusedMap1831=true := by decide +kernel
theorem certified1831 : Certified (graph core1831) (root 10) 0 0 :=
  of_native_maps core1831 DegreeOneSmallSpectrum1203.graph DegreeOneSmallSpectrum905.graph
    sourceMap1831 fusedMap1831 sourceMap1831_checked fusedMap1831_checked
    DegreeOneSmallComparisons.comparison1831
#print axioms sourceMap1831_checked
#print axioms fusedMap1831_checked
#print axioms certified1831
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
