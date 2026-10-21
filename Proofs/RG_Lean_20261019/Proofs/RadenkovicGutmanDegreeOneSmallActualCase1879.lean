/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1879 : Family 10 := level10.get ⟨145,by decide⟩
def sourceMap1879 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1879 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1879_checked : acceptsGraphIso
    (source (graph core1879) (root 10) 0 0) DegreeOneSmallSpectrum1288.graph sourceMap1879=true := by decide +kernel
theorem fusedMap1879_checked : acceptsGraphIso
    (fused (graph core1879) (root 10) 0 0) DegreeOneSmallSpectrum967.graph fusedMap1879=true := by decide +kernel
theorem certified1879 : Certified (graph core1879) (root 10) 0 0 :=
  of_native_maps core1879 DegreeOneSmallSpectrum1288.graph DegreeOneSmallSpectrum967.graph
    sourceMap1879 fusedMap1879 sourceMap1879_checked fusedMap1879_checked
    DegreeOneSmallComparisons.comparison1879
#print axioms sourceMap1879_checked
#print axioms fusedMap1879_checked
#print axioms certified1879
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
