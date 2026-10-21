/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1809 : Family 10 := level10.get ⟨49,by decide⟩
def sourceMap1809 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1809 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1809_checked : acceptsGraphIso
    (source (graph core1809) (root 10) 0 0) DegreeOneSmallSpectrum872.graph sourceMap1809=true := by decide +kernel
theorem fusedMap1809_checked : acceptsGraphIso
    (fused (graph core1809) (root 10) 0 0) DegreeOneSmallSpectrum956.graph fusedMap1809=true := by decide +kernel
theorem certified1809 : Certified (graph core1809) (root 10) 0 0 :=
  of_native_maps core1809 DegreeOneSmallSpectrum872.graph DegreeOneSmallSpectrum956.graph
    sourceMap1809 fusedMap1809 sourceMap1809_checked fusedMap1809_checked
    DegreeOneSmallComparisons.comparison1809
#print axioms sourceMap1809_checked
#print axioms fusedMap1809_checked
#print axioms certified1809
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
