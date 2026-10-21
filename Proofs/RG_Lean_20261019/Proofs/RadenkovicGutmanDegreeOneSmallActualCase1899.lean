/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1899 : Family 10 := level10.get ⟨173,by decide⟩
def sourceMap1899 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,8,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1899 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1899_checked : acceptsGraphIso
    (source (graph core1899) (root 10) 0 0) DegreeOneSmallSpectrum1124.graph sourceMap1899=true := by decide +kernel
theorem fusedMap1899_checked : acceptsGraphIso
    (fused (graph core1899) (root 10) 0 0) DegreeOneSmallSpectrum953.graph fusedMap1899=true := by decide +kernel
theorem certified1899 : Certified (graph core1899) (root 10) 0 0 :=
  of_native_maps core1899 DegreeOneSmallSpectrum1124.graph DegreeOneSmallSpectrum953.graph
    sourceMap1899 fusedMap1899 sourceMap1899_checked fusedMap1899_checked
    DegreeOneSmallComparisons.comparison1899
#print axioms sourceMap1899_checked
#print axioms fusedMap1899_checked
#print axioms certified1899
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
