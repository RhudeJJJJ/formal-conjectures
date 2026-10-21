/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1968 : Family 10 := level10.get ⟨286,by decide⟩
def sourceMap1968 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1968 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1968_checked : acceptsGraphIso
    (source (graph core1968) (root 10) 0 0) DegreeOneSmallSpectrum1252.graph sourceMap1968=true := by decide +kernel
theorem fusedMap1968_checked : acceptsGraphIso
    (fused (graph core1968) (root 10) 0 0) DegreeOneSmallSpectrum1306.graph fusedMap1968=true := by decide +kernel
theorem certified1968 : Certified (graph core1968) (root 10) 0 0 :=
  of_native_maps core1968 DegreeOneSmallSpectrum1252.graph DegreeOneSmallSpectrum1306.graph
    sourceMap1968 fusedMap1968 sourceMap1968_checked fusedMap1968_checked
    DegreeOneSmallComparisons.comparison1968
#print axioms sourceMap1968_checked
#print axioms fusedMap1968_checked
#print axioms certified1968
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
