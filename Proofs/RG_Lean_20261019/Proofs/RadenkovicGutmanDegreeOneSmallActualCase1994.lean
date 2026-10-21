/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1994 : Family 10 := level10.get ⟨324,by decide⟩
def sourceMap1994 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1994 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1994_checked : acceptsGraphIso
    (source (graph core1994) (root 10) 0 0) DegreeOneSmallSpectrum1266.graph sourceMap1994=true := by decide +kernel
theorem fusedMap1994_checked : acceptsGraphIso
    (fused (graph core1994) (root 10) 0 0) DegreeOneSmallSpectrum1403.graph fusedMap1994=true := by decide +kernel
theorem certified1994 : Certified (graph core1994) (root 10) 0 0 :=
  of_native_maps core1994 DegreeOneSmallSpectrum1266.graph DegreeOneSmallSpectrum1403.graph
    sourceMap1994 fusedMap1994 sourceMap1994_checked fusedMap1994_checked
    DegreeOneSmallComparisons.comparison1994
#print axioms sourceMap1994_checked
#print axioms fusedMap1994_checked
#print axioms certified1994
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
