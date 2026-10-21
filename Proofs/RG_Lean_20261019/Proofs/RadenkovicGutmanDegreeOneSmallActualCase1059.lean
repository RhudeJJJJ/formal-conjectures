/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1059 : Family 8 := level8.get ⟨132,by decide⟩
def sourceMap1059 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1059 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1059_checked : acceptsGraphIso
    (source (graph core1059) (root 8) 0 0) DegreeOneSmallSpectrum303.graph sourceMap1059=true := by decide +kernel
theorem fusedMap1059_checked : acceptsGraphIso
    (fused (graph core1059) (root 8) 0 0) DegreeOneSmallSpectrum318.graph fusedMap1059=true := by decide +kernel
theorem certified1059 : Certified (graph core1059) (root 8) 0 0 :=
  of_native_maps core1059 DegreeOneSmallSpectrum303.graph DegreeOneSmallSpectrum318.graph
    sourceMap1059 fusedMap1059 sourceMap1059_checked fusedMap1059_checked
    DegreeOneSmallComparisons.comparison1059
#print axioms sourceMap1059_checked
#print axioms fusedMap1059_checked
#print axioms certified1059
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
