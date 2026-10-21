/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1038 : Family 8 := level8.get ⟨115,by decide⟩
def sourceMap1038 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 8 1 1 v)
def fusedMap1038 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1038_checked : acceptsGraphIso
    (source (graph core1038) (root 8) 1 1) DegreeOneSmallSpectrum1822.graph sourceMap1038=true := by decide +kernel
theorem fusedMap1038_checked : acceptsGraphIso
    (fused (graph core1038) (root 8) 1 1) DegreeOneSmallSpectrum1142.graph fusedMap1038=true := by decide +kernel
theorem certified1038 : Certified (graph core1038) (root 8) 1 1 :=
  of_native_maps core1038 DegreeOneSmallSpectrum1822.graph DegreeOneSmallSpectrum1142.graph
    sourceMap1038 fusedMap1038 sourceMap1038_checked fusedMap1038_checked
    DegreeOneSmallComparisons.comparison1038
#print axioms sourceMap1038_checked
#print axioms fusedMap1038_checked
#print axioms certified1038
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
