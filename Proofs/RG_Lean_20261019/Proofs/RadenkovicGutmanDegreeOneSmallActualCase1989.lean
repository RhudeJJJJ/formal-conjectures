/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1989 : Family 10 := level10.get ⟨315,by decide⟩
def sourceMap1989 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1989 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1989_checked : acceptsGraphIso
    (source (graph core1989) (root 10) 0 0) DegreeOneSmallSpectrum1220.graph sourceMap1989=true := by decide +kernel
theorem fusedMap1989_checked : acceptsGraphIso
    (fused (graph core1989) (root 10) 0 0) DegreeOneSmallSpectrum1393.graph fusedMap1989=true := by decide +kernel
theorem certified1989 : Certified (graph core1989) (root 10) 0 0 :=
  of_native_maps core1989 DegreeOneSmallSpectrum1220.graph DegreeOneSmallSpectrum1393.graph
    sourceMap1989 fusedMap1989 sourceMap1989_checked fusedMap1989_checked
    DegreeOneSmallComparisons.comparison1989
#print axioms sourceMap1989_checked
#print axioms fusedMap1989_checked
#print axioms certified1989
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
