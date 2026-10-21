/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1869 : Family 10 := level10.get ⟨129,by decide⟩
def sourceMap1869 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1869 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1869_checked : acceptsGraphIso
    (source (graph core1869) (root 10) 0 0) DegreeOneSmallSpectrum1179.graph sourceMap1869=true := by decide +kernel
theorem fusedMap1869_checked : acceptsGraphIso
    (fused (graph core1869) (root 10) 0 0) DegreeOneSmallSpectrum954.graph fusedMap1869=true := by decide +kernel
theorem certified1869 : Certified (graph core1869) (root 10) 0 0 :=
  of_native_maps core1869 DegreeOneSmallSpectrum1179.graph DegreeOneSmallSpectrum954.graph
    sourceMap1869 fusedMap1869 sourceMap1869_checked fusedMap1869_checked
    DegreeOneSmallComparisons.comparison1869
#print axioms sourceMap1869_checked
#print axioms fusedMap1869_checked
#print axioms certified1869
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
