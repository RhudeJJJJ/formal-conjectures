/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2232 : Family 10 := level10.get ⟨772,by decide⟩
def sourceMap2232 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2232 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2232_checked : acceptsGraphIso
    (source (graph core2232) (root 10) 0 0) DegreeOneSmallSpectrum1874.graph sourceMap2232=true := by decide +kernel
theorem fusedMap2232_checked : acceptsGraphIso
    (fused (graph core2232) (root 10) 0 0) DegreeOneSmallSpectrum1405.graph fusedMap2232=true := by decide +kernel
theorem certified2232 : Certified (graph core2232) (root 10) 0 0 :=
  of_native_maps core2232 DegreeOneSmallSpectrum1874.graph DegreeOneSmallSpectrum1405.graph
    sourceMap2232 fusedMap2232 sourceMap2232_checked fusedMap2232_checked
    DegreeOneSmallComparisons.comparison2232
#print axioms sourceMap2232_checked
#print axioms fusedMap2232_checked
#print axioms certified2232
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
