/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1896 : Family 10 := level10.get ⟨169,by decide⟩
def sourceMap1896 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,6,7,8,4,5] (sourceLabel 10 0 0 v)
def fusedMap1896 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1896_checked : acceptsGraphIso
    (source (graph core1896) (root 10) 0 0) DegreeOneSmallSpectrum1216.graph sourceMap1896=true := by decide +kernel
theorem fusedMap1896_checked : acceptsGraphIso
    (fused (graph core1896) (root 10) 0 0) DegreeOneSmallSpectrum972.graph fusedMap1896=true := by decide +kernel
theorem certified1896 : Certified (graph core1896) (root 10) 0 0 :=
  of_native_maps core1896 DegreeOneSmallSpectrum1216.graph DegreeOneSmallSpectrum972.graph
    sourceMap1896 fusedMap1896 sourceMap1896_checked fusedMap1896_checked
    DegreeOneSmallComparisons.comparison1896
#print axioms sourceMap1896_checked
#print axioms fusedMap1896_checked
#print axioms certified1896
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
