/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1821 : Family 10 := level10.get ⟨65,by decide⟩
def sourceMap1821 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1821 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1821_checked : acceptsGraphIso
    (source (graph core1821) (root 10) 0 0) DegreeOneSmallSpectrum1159.graph sourceMap1821=true := by decide +kernel
theorem fusedMap1821_checked : acceptsGraphIso
    (fused (graph core1821) (root 10) 0 0) DegreeOneSmallSpectrum877.graph fusedMap1821=true := by decide +kernel
theorem certified1821 : Certified (graph core1821) (root 10) 0 0 :=
  of_native_maps core1821 DegreeOneSmallSpectrum1159.graph DegreeOneSmallSpectrum877.graph
    sourceMap1821 fusedMap1821 sourceMap1821_checked fusedMap1821_checked
    DegreeOneSmallComparisons.comparison1821
#print axioms sourceMap1821_checked
#print axioms fusedMap1821_checked
#print axioms certified1821
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
