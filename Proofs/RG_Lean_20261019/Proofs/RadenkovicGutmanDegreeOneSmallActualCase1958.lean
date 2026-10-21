/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1958 : Family 10 := level10.get ⟨264,by decide⟩
def sourceMap1958 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap1958 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1958_checked : acceptsGraphIso
    (source (graph core1958) (root 10) 0 0) DegreeOneSmallSpectrum1213.graph sourceMap1958=true := by decide +kernel
theorem fusedMap1958_checked : acceptsGraphIso
    (fused (graph core1958) (root 10) 0 0) DegreeOneSmallSpectrum1291.graph fusedMap1958=true := by decide +kernel
theorem certified1958 : Certified (graph core1958) (root 10) 0 0 :=
  of_native_maps core1958 DegreeOneSmallSpectrum1213.graph DegreeOneSmallSpectrum1291.graph
    sourceMap1958 fusedMap1958 sourceMap1958_checked fusedMap1958_checked
    DegreeOneSmallComparisons.comparison1958
#print axioms sourceMap1958_checked
#print axioms fusedMap1958_checked
#print axioms certified1958
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
