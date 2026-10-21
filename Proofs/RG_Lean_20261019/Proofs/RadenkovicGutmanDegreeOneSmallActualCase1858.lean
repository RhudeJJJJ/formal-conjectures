/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1858 : Family 10 := level10.get ⟨114,by decide⟩
def sourceMap1858 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1858 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1858_checked : acceptsGraphIso
    (source (graph core1858) (root 10) 0 0) DegreeOneSmallSpectrum1108.graph sourceMap1858=true := by decide +kernel
theorem fusedMap1858_checked : acceptsGraphIso
    (fused (graph core1858) (root 10) 0 0) DegreeOneSmallSpectrum937.graph fusedMap1858=true := by decide +kernel
theorem certified1858 : Certified (graph core1858) (root 10) 0 0 :=
  of_native_maps core1858 DegreeOneSmallSpectrum1108.graph DegreeOneSmallSpectrum937.graph
    sourceMap1858 fusedMap1858 sourceMap1858_checked fusedMap1858_checked
    DegreeOneSmallComparisons.comparison1858
#print axioms sourceMap1858_checked
#print axioms fusedMap1858_checked
#print axioms certified1858
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
