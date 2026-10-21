/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1939 : Family 10 := level10.get ⟨235,by decide⟩
def sourceMap1939 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1939 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1939_checked : acceptsGraphIso
    (source (graph core1939) (root 10) 0 0) DegreeOneSmallSpectrum1102.graph sourceMap1939=true := by decide +kernel
theorem fusedMap1939_checked : acceptsGraphIso
    (fused (graph core1939) (root 10) 0 0) DegreeOneSmallSpectrum1177.graph fusedMap1939=true := by decide +kernel
theorem certified1939 : Certified (graph core1939) (root 10) 0 0 :=
  of_native_maps core1939 DegreeOneSmallSpectrum1102.graph DegreeOneSmallSpectrum1177.graph
    sourceMap1939 fusedMap1939 sourceMap1939_checked fusedMap1939_checked
    DegreeOneSmallComparisons.comparison1939
#print axioms sourceMap1939_checked
#print axioms fusedMap1939_checked
#print axioms certified1939
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
