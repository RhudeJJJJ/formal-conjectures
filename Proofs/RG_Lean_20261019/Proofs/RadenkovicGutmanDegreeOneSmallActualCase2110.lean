/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2110 : Family 10 := level10.get ⟨535,by decide⟩
def sourceMap2110 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2110 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2110_checked : acceptsGraphIso
    (source (graph core2110) (root 10) 0 0) DegreeOneSmallSpectrum1682.graph sourceMap2110=true := by decide +kernel
theorem fusedMap2110_checked : acceptsGraphIso
    (fused (graph core2110) (root 10) 0 0) DegreeOneSmallSpectrum1039.graph fusedMap2110=true := by decide +kernel
theorem certified2110 : Certified (graph core2110) (root 10) 0 0 :=
  of_native_maps core2110 DegreeOneSmallSpectrum1682.graph DegreeOneSmallSpectrum1039.graph
    sourceMap2110 fusedMap2110 sourceMap2110_checked fusedMap2110_checked
    DegreeOneSmallComparisons.comparison2110
#print axioms sourceMap2110_checked
#print axioms fusedMap2110_checked
#print axioms certified2110
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
