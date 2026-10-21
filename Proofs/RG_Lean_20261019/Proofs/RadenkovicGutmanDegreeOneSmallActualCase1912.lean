/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1912 : Family 10 := level10.get ⟨198,by decide⟩
def sourceMap1912 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1912 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1912_checked : acceptsGraphIso
    (source (graph core1912) (root 10) 0 0) DegreeOneSmallSpectrum1029.graph sourceMap1912=true := by decide +kernel
theorem fusedMap1912_checked : acceptsGraphIso
    (fused (graph core1912) (root 10) 0 0) DegreeOneSmallSpectrum1037.graph fusedMap1912=true := by decide +kernel
theorem certified1912 : Certified (graph core1912) (root 10) 0 0 :=
  of_native_maps core1912 DegreeOneSmallSpectrum1029.graph DegreeOneSmallSpectrum1037.graph
    sourceMap1912 fusedMap1912 sourceMap1912_checked fusedMap1912_checked
    DegreeOneSmallComparisons.comparison1912
#print axioms sourceMap1912_checked
#print axioms fusedMap1912_checked
#print axioms certified1912
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
