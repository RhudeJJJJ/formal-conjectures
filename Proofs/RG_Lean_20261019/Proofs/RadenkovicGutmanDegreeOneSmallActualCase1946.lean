/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1946 : Family 10 := level10.get ⟨246,by decide⟩
def sourceMap1946 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1946 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1946_checked : acceptsGraphIso
    (source (graph core1946) (root 10) 0 0) DegreeOneSmallSpectrum1213.graph sourceMap1946=true := by decide +kernel
theorem fusedMap1946_checked : acceptsGraphIso
    (fused (graph core1946) (root 10) 0 0) DegreeOneSmallSpectrum1216.graph fusedMap1946=true := by decide +kernel
theorem certified1946 : Certified (graph core1946) (root 10) 0 0 :=
  of_native_maps core1946 DegreeOneSmallSpectrum1213.graph DegreeOneSmallSpectrum1216.graph
    sourceMap1946 fusedMap1946 sourceMap1946_checked fusedMap1946_checked
    DegreeOneSmallComparisons.comparison1946
#print axioms sourceMap1946_checked
#print axioms fusedMap1946_checked
#print axioms certified1946
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
