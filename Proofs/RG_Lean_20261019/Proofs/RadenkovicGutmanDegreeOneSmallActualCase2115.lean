/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2115 : Family 10 := level10.get ⟨542,by decide⟩
def sourceMap2115 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,10,11,8,9] (sourceLabel 10 0 0 v)
def fusedMap2115 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2115_checked : acceptsGraphIso
    (source (graph core2115) (root 10) 0 0) DegreeOneSmallSpectrum1675.graph sourceMap2115=true := by decide +kernel
theorem fusedMap2115_checked : acceptsGraphIso
    (fused (graph core2115) (root 10) 0 0) DegreeOneSmallSpectrum1056.graph fusedMap2115=true := by decide +kernel
theorem certified2115 : Certified (graph core2115) (root 10) 0 0 :=
  of_native_maps core2115 DegreeOneSmallSpectrum1675.graph DegreeOneSmallSpectrum1056.graph
    sourceMap2115 fusedMap2115 sourceMap2115_checked fusedMap2115_checked
    DegreeOneSmallComparisons.comparison2115
#print axioms sourceMap2115_checked
#print axioms fusedMap2115_checked
#print axioms certified2115
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
