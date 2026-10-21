/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1875 : Family 10 := level10.get ⟨137,by decide⟩
def sourceMap1875 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1875 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1875_checked : acceptsGraphIso
    (source (graph core1875) (root 10) 0 0) DegreeOneSmallSpectrum1225.graph sourceMap1875=true := by decide +kernel
theorem fusedMap1875_checked : acceptsGraphIso
    (fused (graph core1875) (root 10) 0 0) DegreeOneSmallSpectrum964.graph fusedMap1875=true := by decide +kernel
theorem certified1875 : Certified (graph core1875) (root 10) 0 0 :=
  of_native_maps core1875 DegreeOneSmallSpectrum1225.graph DegreeOneSmallSpectrum964.graph
    sourceMap1875 fusedMap1875 sourceMap1875_checked fusedMap1875_checked
    DegreeOneSmallComparisons.comparison1875
#print axioms sourceMap1875_checked
#print axioms fusedMap1875_checked
#print axioms certified1875
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
