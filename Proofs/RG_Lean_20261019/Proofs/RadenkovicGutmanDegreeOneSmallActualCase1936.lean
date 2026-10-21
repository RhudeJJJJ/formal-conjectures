/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1936 : Family 10 := level10.get ⟨231,by decide⟩
def sourceMap1936 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap1936 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1936_checked : acceptsGraphIso
    (source (graph core1936) (root 10) 0 0) DegreeOneSmallSpectrum1160.graph sourceMap1936=true := by decide +kernel
theorem fusedMap1936_checked : acceptsGraphIso
    (fused (graph core1936) (root 10) 0 0) DegreeOneSmallSpectrum1181.graph fusedMap1936=true := by decide +kernel
theorem certified1936 : Certified (graph core1936) (root 10) 0 0 :=
  of_native_maps core1936 DegreeOneSmallSpectrum1160.graph DegreeOneSmallSpectrum1181.graph
    sourceMap1936 fusedMap1936 sourceMap1936_checked fusedMap1936_checked
    DegreeOneSmallComparisons.comparison1936
#print axioms sourceMap1936_checked
#print axioms fusedMap1936_checked
#print axioms certified1936
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
