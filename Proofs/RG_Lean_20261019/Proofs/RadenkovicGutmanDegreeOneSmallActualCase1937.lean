/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1937 : Family 10 := level10.get ⟨232,by decide⟩
def sourceMap1937 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap1937 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1937_checked : acceptsGraphIso
    (source (graph core1937) (root 10) 0 0) DegreeOneSmallSpectrum1161.graph sourceMap1937=true := by decide +kernel
theorem fusedMap1937_checked : acceptsGraphIso
    (fused (graph core1937) (root 10) 0 0) DegreeOneSmallSpectrum1182.graph fusedMap1937=true := by decide +kernel
theorem certified1937 : Certified (graph core1937) (root 10) 0 0 :=
  of_native_maps core1937 DegreeOneSmallSpectrum1161.graph DegreeOneSmallSpectrum1182.graph
    sourceMap1937 fusedMap1937 sourceMap1937_checked fusedMap1937_checked
    DegreeOneSmallComparisons.comparison1937
#print axioms sourceMap1937_checked
#print axioms fusedMap1937_checked
#print axioms certified1937
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
